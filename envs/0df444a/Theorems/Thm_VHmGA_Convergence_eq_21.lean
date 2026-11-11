-- Prove2me | Theorems.Thm_VHmGA_Convergence_eq_21
-- name    : VHmGA.Convergence.eq_21
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:40:12.288291+00:00
-- url     : https://prove2.me/theorems/0ebaaff4-22af-4d6d-84b7-2a74711c9295
-- title:
--   §8.2, eq. (21) — conditional expected descent bound (corrected: unbiased aggregate)
-- statement:
--   Throughout, $F:\mathbb R^d\to\mathbb R$ is $L$-smooth with gradient map $g=\nabla F$ and $L>0$, i.e. $\|\nabla F(w)-\nabla F(w')\|\le L\|w-w'\|$ for all $w,w'$. On a probability space $(\Omega,\mathcal F,\mathbb P)$ the iterates follow the update (18), $w_{t+1}=w_t-\eta_t\tilde g_t$, from a fixed starting point $w_1$, with step sizes $\eta_t>0$. For each $t\ge1$ a $\sigma$-algebra $\mathcal G_t\subseteq\mathcal F$ is fixed with respect to which $w_t$ is measurable (the paper's "conditioning on $w_t$"; $\mathcal G_t=\sigma(w_t)$ or the history up to $t$ are both allowed). The aggregate $\tilde g_t$ is integrable and conditionally unbiased, $\mathbb E[\tilde g_t\mid\mathcal G_t]=\nabla F(w_t)$, and its conditional mean-square error obeys (19):
--   $$
--   \mathbb E\big[\|\tilde g_t-\nabla F(w_t)\|^2\,\big|\,\mathcal G_t\big]\le\sigma^2_{\mathrm{total}}=\sigma^2+\sigma^2_{\mathrm{DP}}+\frac{\alpha}{1-\alpha}\sigma_a^2,\qquad 0\le\alpha<1 .
--   $$
--   Below, $\mathbb E[\,\cdot\mid w_t]$ means $\mathbb E[\,\cdot\mid\mathcal G_t]$.
--
--   Then for every $t\ge1$, $F(w_{t+1})$ and $\|\tilde g_t\|^2$ are integrable and, almost surely,
--   $$
--   \mathbb E[F(w_{t+1})\mid w_t]\le F(w_t)-\eta_t\|\nabla F(w_t)\|^2+\frac{L\eta_t^2}{2}\,\mathbb E\big[\|\tilde g_t\|^2\,\big|\,w_t\big].
--   $$
--
--   This is the paper's eq. (21): the descent lemma (20) applied along the update (18), conditioned on the current iterate. The printed text derives it by "substituting the parameter update rule from Equation 1 into the smoothness inequality"; "Equation 1" refers to the update (18) and the smoothness inequality is (20). It is the first step of the proof of Theorem 8.1.
--
--   **Formalization Note** The step size is the general sequence $\eta_t>0$ of §8.1; no bound on $\eta_t$ is needed here.
--
--   Differences from the source:
--   - correction: the only hypotheses on the aggregate are L-smoothness of F and the conditional MSE bound (19); 'unbiased' is said of honest workers' gradients only → the run also assumes E[g̃_t | G_t] = ∇F(w_t) a.s.; reason: under (19) alone the statement is false: d = 1, F(w) = w²/2 (L = 1, F* = 0), g̃_t ≡ w_t + s with s > 0, w_1 = −s gives w_t ≡ −s, conditional MSE s² = σ²_total (σ = s, σ_DP = σ_a = α = 0), and violates the inequality; the paper's proof uses unbiasedness to remove the cross term in (21) and for the equality in (23)
--   - generalization: conditioning on w_t ('accounts for the parameter history up to iteration t') → conditioning on any σ-algebra G_t ⊆ F for which w_t is G_t-measurable; reason: σ(w_t) and the history σ-algebra are both admissible G_t, so the paper's statement is an instance
--   - generalization: corrupted fraction α < 1/3 → 0 ≤ α < 1; reason: the bound only needs α/(1−α) to be defined; α ∈ [0, 1/3) is an instance
--   - generalization: F is the global risk (1), a finite sum of local risks → F is any L-smooth function ℝ^d → ℝ; reason: only L-smoothness is used; the finite sum (1) with an L-smooth total is an instance
--   - encoding: expectations of F(w_t), ‖∇F(w_t)‖² and ‖g̃_t‖² are used without comment → their integrability is asserted as additional conclusions; reason: Lean's integral and conditional expectation of a non-integrable function are 0; asserting integrability makes the inequality about the genuine expectations and does not change any instance
--   - encoding: σ², σ²_DP, σ²_a are variances (nonnegative reals) → squares σ^2, σDP^2, σa^2 of real parameters σ, σDP, σa; reason: every nonnegative real is the square of a real, so the set of admissible values of σ²_total is the same
-- source:
--   Jean Rosemond Dora, Ladislav Hluchý, STOC 2027 submission #955 (October 2026), §8.2, eq. (21), p. 6

import Mathlib
import Definitions.Def_ConvexOptAlg_SmoothGD_Defs
import Definitions.Def_VHmGA_Convergence_Defs

set_option autoImplicit false
open MeasureTheory

namespace VHmGA.Convergence

theorem eq_21 {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {F : EuclideanSpace ℝ (Fin d) → ℝ}
    {g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)} {L : ℝ} {η : ℕ → ℝ}
    {σ σDP σa α : ℝ} {w1 : EuclideanSpace ℝ (Fin d)}
    {w gt : ℕ → Ω → EuclideanSpace ℝ (Fin d)} {m : ℕ → MeasurableSpace Ω}
    (hF : ConvexOptAlg.SmoothGD.IsBetaSmooth F g L) (hL : 0 < L)
    (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hrun : IsVerifiedSGDRun μ g η w1 w gt m (sigmaTotalSq σ σDP σa α))
    (t : ℕ) (ht : 1 ≤ t) :
    Integrable (fun ω => F (w (t + 1) ω)) μ ∧
    Integrable (fun ω => ‖gt t ω‖ ^ 2) μ ∧
    μ[fun ω => F (w (t + 1) ω) | m t] ≤ᵐ[μ] fun ω =>
      F (w t ω) - η t * ‖g (w t ω)‖ ^ 2 +
        L * η t ^ 2 / 2 * μ[fun ω' => ‖gt t ω'‖ ^ 2 | m t] ω := by sorry

end VHmGA.Convergence
