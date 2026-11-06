-- Prove2me | Theorems.Thm_RollingProbeQN_Convex_lemma_E_3
-- name    : RollingProbeQN.Convex.lemma_E_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:28:08.042914+00:00
-- url     : https://prove2.me/theorems/5a575fb4-77fe-486a-af5e-1585a02a90dd
-- title:
--   Lemma E.3 — monotonicity of $a(\lambda)$, $m(\lambda)$ and transport of the certificate to $y(\lambda)$
-- statement:
--   Under Assumption 2.1, run Algorithm 1 with any $b>0$, $\sigma\in(0,1)$, and fix an executed iteration $k$, with mass $A_k$, $\zeta_k=\|z_k-x_k\|$, model $B_k$ and certificate $\bar E_k$. For $\lambda>0$ let $a(\lambda)$, $y(\lambda)$ be as in (1) and $m(\lambda)=a(\lambda)\zeta_k/(A_k+a(\lambda))$. Then $m(\lambda)=\|y(\lambda)-x_k\|$, and:
--
--   1. $a$ is continuous and strictly increasing on $(0,\infty)$, $a(\lambda)\to0$ as $\lambda\to0^+$ and $a(\lambda)\to\infty$ as $\lambda\to\infty$;
--   2. $m$ is continuous and nondecreasing on $(0,\infty)$, $m(\lambda)\to0$ as $\lambda\to0^+$, and $m(c\lambda)\le c\,m(\lambda)$ for every $c\ge1$;
--   3. for every $\lambda>0$,
--   $$\|B_k-H(y(\lambda))\|_{\mathrm{op}}\le\min\{L_1,\bar E_k+L_2m(\lambda)\},\qquad \Big\|B_k-\int_0^1H\big(x_k+s(y(\lambda)-x_k)\big)\,ds\Big\|_{\mathrm{op}}\le\bar E_k+\frac{L_2}{2}m(\lambda).$$
--
--   These properties make the surrogate (10) monotone in $\lambda$ and bound the first term of (6).
--
--   Differences from the source:
--   - encoding: the lemma's hypotheses B_k ∈ Z and ‖B_k − H(x_k)‖op ≤ Ē_k (Lemma E.1) → not hypotheses: the statement is about the run, where they hold; reason: they hold at every executed iteration by (4) and Lemma E.1, so no instance of Algorithm 1 changes
--   - encoding: Step 1 returns x_k when ∇f(x_k) = 0; the iterates after a return do not exist → the run is frozen at the return; statements about an iteration assume it is executed (Active); reason: B_k, Ē_k, λ_k, y_k, r_k are formed only at executed iterations (reading R2)
--   - encoding: refreshed group i_k = (k mod χ) + 1, groups g_1, …, g_χ → 0-based label k % χ of grp : Fin d → Fin χ; reason: relabelling of the groups (reading R5)
--   - encoding: Π_Z clips the eigenvalues of a symmetric matrix to [0, L₁] → clipZ L₁, the functional calculus of t ↦ min (max t 0) L₁ (0 on non-symmetric input); reason: the same map on symmetric matrices, the only input it receives (reading R6)
--   - encoding: a partition g₁, …, g_χ of [d] → a surjective map grp : Fin d → Fin χ with 0 < χ; reason: a partition has no empty block (reading R7)
--   - encoding: the while loop of Subroutine 1.1 → a guarded bisection pass iterated ⌈4 log(L₁/Ē_k)/log 2⌉ + 1 times; reason: the loop ends within that many passes (Lemma E.6's count) and further passes change nothing (reading R8)
-- source:
--   Mokhtari, Patitucci, Improved Gradient Complexity for Quasi-Newton Proximal Extragradient Methods via Certified Curvature Reuse, arXiv:2610.40608, Lemma E.3, p. 45

import Mathlib
import Definitions.Def_RollingProbeQN_Convex_Assumption21
import Definitions.Def_RollingProbeQN_Convex_iterAt
import Definitions.Def_RollingProbeQN_Convex_Active
import Definitions.Def_RollingProbeQN_Convex_mOf

namespace RollingProbeQN.Convex

/-- **Lemma E.3 (Monotonicity and transport).**
Mokhtari, Patitucci, *Improved Gradient Complexity for Quasi-Newton Proximal Extragradient
Methods via Certified Curvature Reuse*, arXiv:2610.40608, Lemma E.3, p. 45: "Fix an iteration `k` of Algorithm 1, with mass `A_k ≥ 0`,
`ζ_k = ‖z_k − x_k‖`, model `B_k ∈ Z`, and certificate `Ē_k` satisfying `‖B_k − H(x_k)‖op ≤ Ē_k`
(Lemma E.1). For `λ > 0` let `a(λ)` […], `y(λ)` […], and let `m(λ) = ‖y(λ) − x_k‖ = a(λ)/(A_k + a(λ)) ζ_k`
be the displacement of (7). Then: (i) `a` is continuous and strictly increasing on `(0, ∞)`, with
`a(λ) → 0` as `λ → 0+` and `a(λ) → ∞` as `λ → ∞`; (ii) `m` is continuous and nondecreasing,
`m(λ) → 0` as `λ → 0+`, and `m(cλ) ≤ c m(λ)` for every `c ≥ 1`; (iii) (transport) for every
`λ > 0`, `‖B_k − H(y(λ))‖op ≤ min{L1, Ē_k + L2 m(λ)} = E_k(λ)`,
`‖B_k − ∫_0^1 H(x_k + s(y(λ) − x_k)) ds‖op ≤ Ē_k + (L2/2) m(λ)`."

The statement also records the identity `‖y(λ) − x_k‖ = m(λ)` of (7).

**Formalization Note.** The run is `run cfg (gradient f) x₀` with `cfg = ⟨grp, S, L₁, L₂, b, σ⟩`, for
any allowance `b > 0` and `σ ∈ (0, 1)` (Algorithm 1 fixes `b > 0`, p. 9); `st` is the state at the
start of iteration `k` and `D` the quantities of iteration `k`. "An iteration `k` of Algorithm 1" is an
executed iteration (`Active`: the run has not returned and `∇f(x_k) ≠ 0`). The hypotheses `B_k ∈ Z` and `‖B_k − H(x_k)‖op ≤ Ē_k` of the page hold along the run
(Lemma E.1) and are not repeated. The integral is the Bochner integral of the continuous map
`s ↦ H(x_k + s(y(λ) − x_k))` on `[0, 1]`. -/
theorem lemma_E_3 {d χ : ℕ} {f : EuclideanSpace ℝ (Fin d) → ℝ} {L₁ L₂ R b σ : ℝ}
    {S : Set (Fin d × Fin d)} {grp : Fin d → Fin χ} {x₀ xstar : EuclideanSpace ℝ (Fin d)}
    (hA : Assumption21 d χ f L₁ L₂ R S grp x₀ xstar) (hb : 0 < b) (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (k : ℕ) (hk : Active (⟨grp, S, L₁, L₂, b, σ⟩ : Config d χ) (gradient f) x₀ k) :
    let cfg : Config d χ := ⟨grp, S, L₁, L₂, b, σ⟩
    let st := run cfg (gradient f) x₀ k
    let D := iterAt cfg (gradient f) x₀ k
    (ContinuousOn (aOf st.A) (Set.Ioi 0) ∧ StrictMonoOn (aOf st.A) (Set.Ioi 0) ∧
      Filter.Tendsto (aOf st.A) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) ∧
      Filter.Tendsto (aOf st.A) Filter.atTop Filter.atTop) ∧
    ((∀ lam : ℝ, 0 < lam → ‖yOf st.A st.x st.z lam - st.x‖ = mOf st.A ‖st.z - st.x‖ lam) ∧
      ContinuousOn (mOf st.A ‖st.z - st.x‖) (Set.Ioi 0) ∧
      MonotoneOn (mOf st.A ‖st.z - st.x‖) (Set.Ioi 0) ∧
      Filter.Tendsto (mOf st.A ‖st.z - st.x‖) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) ∧
      ∀ c : ℝ, 1 ≤ c → ∀ lam : ℝ, 0 < lam →
        mOf st.A ‖st.z - st.x‖ (c * lam) ≤ c * mOf st.A ‖st.z - st.x‖ lam) ∧
    (∀ lam : ℝ, 0 < lam →
      ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) D.B - hess f (yOf st.A st.x st.z lam)‖ ≤
          min L₁ (D.Ebar + L₂ * mOf st.A ‖st.z - st.x‖ lam) ∧
      ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) D.B -
          ∫ s in (0 : ℝ)..1, hess f (st.x + s • (yOf st.A st.x st.z lam - st.x))‖ ≤
          D.Ebar + L₂ / 2 * mOf st.A ‖st.z - st.x‖ lam) := by sorry

end RollingProbeQN.Convex
