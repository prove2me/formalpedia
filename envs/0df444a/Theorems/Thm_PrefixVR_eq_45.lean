-- Prove2me | Theorems.Thm_PrefixVR_eq_45
-- name    : PrefixVR.eq_45
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:37:41.57521+00:00
-- url     : https://prove2.me/theorems/dc0ed6b3-04cf-4fb0-894f-469fabd232e2
-- title:
--   Eqs. (44)–(45) — average stationarity of Algorithm 1 under (44)
-- statement:
--   Let $f_1,\dots,f_n$ and $f=\frac1n\sum_i f_i$ satisfy **Assumption 2** ($f_*=\inf_x f(x)>-\infty$; $\Delta_f=f(x_1)-f_*$) and **Assumption 3** with constants $L_f>0$, $\delta\ge0$. Run Algorithm 1 from $x_1$ with a stepsize $\eta>0$ such that
--   $$
--   L_f\eta+2n\delta^2\eta^2\le1 .\qquad(44)
--   $$
--   Then for every $T\ge1$
--   $$
--   \frac1T\sum_{t=1}^T\mathbb E\|\nabla f(x_t)\|^2\le\frac{2\Delta_f}{\eta T},\qquad(45)
--   $$
--   the expectation being over all estimator samples.
--
--   This is the shared core of Theorems 1 and 2: each follows by checking (44) for its stepsize and converting the average to the random output by (46).
--
--   **Formalization Note** Assumption 2 is `BddBelow (Set.range f)` with $f_*=\inf_x f(x)$ (`⨅ x, f x`); $\nabla f$ is Mathlib's `gradient`.
--
--   Differences from the source:
--   - encoding: Assumption 2: f_* := inf f > −∞ → BddBelow (Set.range f) and f_* = ⨅ x, f x; reason: a real infimum of a set bounded below is the true infimum
--   - encoding: Assumption 3 → Assumption3 fi g Lf δ, with g i the gradient of fi i; reason: see the definition
--   - encoding: the expectation over the estimator samples of the run of Algorithm 1 → the uniform average over the finite sample space Sample n T (output index τ and the draws (j_t, i_t) of updates t ≤ T, with one-point or unused dummy draws where the paper draws nothing), for a horizon T containing every time in the statement; reason: independent uniform draws on finite sets have the uniform product law; unused coordinates and later draws change no expectation of quantities up to the stated times
--   - encoding: components i ∈ [n] = {1, …, n} → Fin n, paper index i is i − 1, with NeZero n; reason: Lean convention; n ≥ 1 is the paper's standing setting of a finite sum
-- source:
--   Jiang, Wang, Yang, Li, Zhang, Memory-efficient Finite-sum Optimization without Full Gradient Refreshes (manuscript, sha256 ed33106a…), App. C, Eqs. (43)–(45), p.16 (PDF p.16)

import Mathlib
import Definitions.Def_ConvexOptAlg_SmoothGD_Defs
import Definitions.Def_KatyushaNs_favg
import Definitions.Def_PrefixVR_Variation
import Definitions.Def_PrefixVR_Assumption3
import Definitions.Def_PrefixVR_step
import Definitions.Def_PrefixVR_Sample
import Definitions.Def_PrefixVR_run

namespace PrefixVR

/-- **Average stationarity under (44).** Jiang, Wang, Yang, Li, Zhang (manuscript, sha256
ed33106a…), App. C, Eqs. (43)–(45), p.16: under Assumptions 2 and 3, whenever
`L_f η + 2nδ²η² ≤ 1` (44), Algorithm 1 satisfies
`(1/T) ∑_{t=1}^T 𝔼‖∇f(x_t)‖² ≤ 2Δ_f/(ηT)` (45), with `Δ_f = f(x₁) − f_*`, `f_* = inf f`.

Stated for every stepsize `η > 0` with (44), every initial point `x₁` and every horizon `T ≥ 1`.

**Formalization Note.** `f = KatyushaNs.favg fi`; Assumption 2 ("f_* := inf f > −∞") is
`BddBelow (Set.range f)` and `f_* = ⨅ x, f x`; Assumption 3 is `Assumption3 fi g Lf δ`, so
`g i x = ∇fᵢ(x)`; `∇f` is Mathlib's `gradient`. Expectations are over `Sample n T`. -/
theorem eq_45 {n d : ℕ} [NeZero n] (fi : Fin n → EuclideanSpace ℝ (Fin d) → ℝ)
    (g : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (Lf δ : ℝ)
    (hA3 : Assumption3 fi g Lf δ) (hA2 : BddBelow (Set.range (KatyushaNs.favg fi)))
    (η : ℝ) (hη : 0 < η) (h44 : Lf * η + 2 * n * δ ^ 2 * η ^ 2 ≤ 1)
    (x₁ : EuclideanSpace ℝ (Fin d)) (T : ℕ) (hT : 1 ≤ T) :
    (T : ℝ)⁻¹ * ∑ t ∈ Finset.Icc 1 T,
        expect (fun ω : Sample n T => ‖gradient (KatyushaNs.favg fi) (xIter g η x₁ ω t)‖ ^ 2)
      ≤ 2 * (KatyushaNs.favg fi x₁ - ⨅ x, KatyushaNs.favg fi x) / (η * T) := by sorry

end PrefixVR
