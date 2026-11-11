-- Prove2me | Theorems.Thm_VHmGA_Convergence_theorem_8_1
-- name    : VHmGA.Convergence.theorem_8_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:40:25.707219+00:00
-- url     : https://prove2.me/theorems/a7d74b0d-2324-4b80-95ec-e3eba7285a93
-- title:
--   Theorem 8.1 — $\frac1T\sum_{t=1}^T\mathbb E\|\nabla F(w_t)\|^2\le\frac{2(F(w_1)-F^*)}{\eta T}+L\eta\sigma^2_{\mathrm{total}}$ (corrected: unbiased aggregate)
-- statement:
--   This is the convergence theorem of the VHmGA framework (Theorem 8.1, with the explicit constant of eq. (28) from its proof).
--
--   Throughout, $F:\mathbb R^d\to\mathbb R$ is $L$-smooth with gradient map $g=\nabla F$ and $L>0$, i.e. $\|\nabla F(w)-\nabla F(w')\|\le L\|w-w'\|$ for all $w,w'$. On a probability space $(\Omega,\mathcal F,\mathbb P)$ the iterates follow the update (18), $w_{t+1}=w_t-\eta_t\tilde g_t$, from a fixed starting point $w_1$, with step sizes $\eta_t>0$. For each $t\ge1$ a $\sigma$-algebra $\mathcal G_t\subseteq\mathcal F$ is fixed with respect to which $w_t$ is measurable (the paper's "conditioning on $w_t$"; $\mathcal G_t=\sigma(w_t)$ or the history up to $t$ are both allowed). The aggregate $\tilde g_t$ is integrable and conditionally unbiased, $\mathbb E[\tilde g_t\mid\mathcal G_t]=\nabla F(w_t)$, and its conditional mean-square error obeys (19):
--   $$
--   \mathbb E\big[\|\tilde g_t-\nabla F(w_t)\|^2\,\big|\,\mathcal G_t\big]\le\sigma^2_{\mathrm{total}}=\sigma^2+\sigma^2_{\mathrm{DP}}+\frac{\alpha}{1-\alpha}\sigma_a^2,\qquad 0\le\alpha<1 .
--   $$
--   Below, $\mathbb E[\,\cdot\mid w_t]$ means $\mathbb E[\,\cdot\mid\mathcal G_t]$.
--
--   Assume moreover that the step is constant, $\eta_t=\eta$ with $0<\eta\le1/L$, and let $F^*$ be a lower bound of $F$: $F^*\le F(w)$ for all $w$. Then for every number of iterations $T\ge1$, $\|\nabla F(w_t)\|^2$ is integrable for $t=1,\dots,T$ and
--   $$
--   \frac1T\sum_{t=1}^{T}\mathbb E\big[\|\nabla F(w_t)\|^2\big]\le\frac{2\,(F(w_1)-F^*)}{\eta T}+L\eta\,\sigma^2_{\mathrm{total}} .
--   $$
--
--   The average squared gradient norm along the trajectory thus decays like $1/T$ up to a noise floor $L\eta\sigma^2_{\mathrm{total}}$, in which the verification layer, the privacy noise and the surviving adversarial contributions enter only through $\sigma^2_{\mathrm{total}}$. For nonconvex $F$ a small average gradient norm is the standard notion of approximate stationarity.
--
--   Differences from the source:
--   - correction: the only hypotheses on the aggregate are L-smoothness of F and the conditional MSE bound (19); 'unbiased' is said of honest workers' gradients only → the run also assumes E[g̃_t | G_t] = ∇F(w_t) a.s.; reason: under (19) alone the statement is false: d = 1, F(w) = w²/2 (L = 1, F* = 0), g̃_t ≡ w_t + s with s > 0, w_1 = −s gives w_t ≡ −s, conditional MSE s² = σ²_total (σ = s, σ_DP = σ_a = α = 0), and violates the inequality; the paper's proof uses unbiasedness to remove the cross term in (21) and for the equality in (23)
--   - generalization: conditioning on w_t ('accounts for the parameter history up to iteration t') → conditioning on any σ-algebra G_t ⊆ F for which w_t is G_t-measurable; reason: σ(w_t) and the history σ-algebra are both admissible G_t, so the paper's statement is an instance
--   - generalization: corrupted fraction α < 1/3 → 0 ≤ α < 1; reason: the bound only needs α/(1−α) to be defined; α ∈ [0, 1/3) is an instance
--   - generalization: F is the global risk (1), a finite sum of local risks → F is any L-smooth function ℝ^d → ℝ; reason: only L-smoothness is used; the finite sum (1) with an L-smooth total is an instance
--   - encoding: expectations of F(w_t), ‖∇F(w_t)‖² and ‖g̃_t‖² are used without comment → their integrability is asserted as additional conclusions; reason: Lean's integral and conditional expectation of a non-integrable function are 0; asserting integrability makes the inequality about the genuine expectations and does not change any instance
--   - encoding: σ², σ²_DP, σ²_a are variances (nonnegative reals) → squares σ^2, σDP^2, σa^2 of real parameters σ, σDP, σa; reason: every nonnegative real is the square of a real, so the set of admissible values of σ²_total is the same
--   - reading: η in (22) is not specified; §8.1 has a time-varying η_t > 0 and the text before the theorem mentions diminishing schedules such as η_t = 1/√t → constant step η_t = η with 0 < η ≤ 1/L; reason: the bound contains a single η and the proof fixes 'a sufficiently small constant learning rate η_t = η ≤ 1/L'; for unrestricted η it is false (F(w) = w²/2, g̃_t = ∇F(w_t), η = 3 gives w_t = (−2)^{t−1} w_1)
--   - generalization: F* = inf_w F(w) → F* is any lower bound of F; reason: inf_w F(w) is a lower bound, so the paper's case is an instance
--   - generalization: upper bound O((F(w_1) − F*)/(ηT) + Lησ²_total) → the explicit bound 2(F(w_1) − F*)/(ηT) + Lησ²_total; reason: this is the paper's own constant from (28); since F(w_1) − F* ≥ 0 and Lησ²_total ≥ 0 it implies (22) with O-constant 2
--   - reading: (28) ends with '= O(1/√T)' → not stated; reason: it is a remark in the proof, not a clause of (22): for fixed η and σ_total > 0 the right side tends to Lησ²_total ≠ 0, so it holds only for a T-dependent step η ∝ 1/√T, which the theorem does not fix
-- source:
--   Jean Rosemond Dora, Ladislav Hluchý, STOC 2027 submission #955 (October 2026), Theorem 8.1, eq. (22), p. 6, with the explicit constant of eq. (28), proof of Theorem 8.1, p. 7

import Mathlib
import Definitions.Def_ConvexOptAlg_SmoothGD_Defs
import Definitions.Def_VHmGA_Convergence_Defs

set_option autoImplicit false
open MeasureTheory

namespace VHmGA.Convergence

theorem theorem_8_1 {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {F : EuclideanSpace ℝ (Fin d) → ℝ}
    {g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)} {L η : ℝ}
    {σ σDP σa α : ℝ} {w1 : EuclideanSpace ℝ (Fin d)}
    {w gt : ℕ → Ω → EuclideanSpace ℝ (Fin d)} {m : ℕ → MeasurableSpace Ω}
    (hF : ConvexOptAlg.SmoothGD.IsBetaSmooth F g L) (hL : 0 < L)
    (hη : 0 < η) (hηL : η ≤ 1 / L) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hrun : IsVerifiedSGDRun μ g (fun _ => η) w1 w gt m (sigmaTotalSq σ σDP σa α))
    {Fstar : ℝ} (hFstar : ∀ x, Fstar ≤ F x) (T : ℕ) (hT : 1 ≤ T) :
    (∀ t ∈ Finset.Icc 1 T, Integrable (fun ω => ‖g (w t ω)‖ ^ 2) μ) ∧
    1 / (T : ℝ) * ∑ t ∈ Finset.Icc 1 T, ∫ ω, ‖g (w t ω)‖ ^ 2 ∂μ ≤
      2 * (F w1 - Fstar) / (η * T) + L * η * sigmaTotalSq σ σDP σa α := by sorry

end VHmGA.Convergence
