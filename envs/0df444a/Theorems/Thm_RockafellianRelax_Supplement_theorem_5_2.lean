-- Prove2me | Theorems.Thm_RockafellianRelax_Supplement_theorem_5_2
-- name    : RockafellianRelax.Supplement.theorem_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T03:20:46.648503+00:00
-- url     : https://prove2.me/theorems/581c962a-a96a-4737-980c-ccab6f4cea81
-- title:
--   Theorem 5.2 — convergence to the first-order optimality condition
-- statement:
--   Let $\varphi:\mathbb R^n\to\overline{\mathbb R}$ be proper, let $f:\mathbb R^m\times\mathbb R^n\to\overline{\mathbb R}$ be an exact Rockafellian for minimizing $\varphi$, supported by $\bar y\in\mathbb R^m$, and let $f^\nu:\mathbb R^m\times\mathbb R^n\to\overline{\mathbb R}$ be functions. Let $\partial$ be the general (limiting) subdifferential, empty where the function is not finite, and consider the condition
--
--   $$
--   \operatorname{LimOut}(\operatorname{gph}\partial f^\nu)\subset\operatorname{gph}\partial f . \tag{5.1}
--   $$
--
--   Consider also sequences $y^\nu\to\bar y$, $\varepsilon^\nu\ge0$ with $\varepsilon^\nu\to0$, and $(u^\nu,x^\nu)$ with $\operatorname{dist}((y^\nu,0),\partial f^\nu(u^\nu,x^\nu))\le\varepsilon^\nu$, where the distance is Euclidean and is $+\infty$ to the empty set.
--
--   1. If (5.1) holds, then every cluster point $(\hat u,\hat x)$ of $\{(u^\nu,x^\nu)\}$ satisfies $(\bar y,0)\in\partial f(\hat u,\hat x)$.
--   2. Suppose in addition that $f$ is strictly exact, supported by $\bar y$, that $f^\nu$ epi-converges to $f$, and that each $f^\nu$ is proper, lower semicontinuous and convex. Then (5.1) holds.
--   3. Under the assumptions of item 2, without assuming (5.1), every cluster point $(\hat u,\hat x)$ satisfies $\hat u=0$ and $\hat x\in\operatorname{argmin}_x\varphi(x)$.
--
--   The theorem justifies solving the approximating problems to first-order stationarity only, and in the convex case it recovers minimizers of the actual problem.
--
--   **Formalization Note** The tolerance condition forces each $\partial f^\nu(u^\nu,x^\nu)$ to be nonempty. Item 2 does not mention the sequences. A cluster point is `MapClusterPt`.
--
--   Differences from the source:
--
--   - reading: every cluster point satisfies the necessary first-order optimality condition in Theorem 5.1 → (ȳ, 0) ∈ ∂f(û, x̂); reason: the paragraph before the theorem (p.24) names this the condition that limits of approximate solutions should satisfy
--   - reading: {f^ν} are strictly limit-exact Rockafellians with f being their limit → f is strictly exact, supported by the same ȳ, and f^ν epi-converges to f; reason: in Definition 3.6 the support is that of f, here ȳ; with another support the claim fails, e.g. m = n = 1, f^ν = f = |u| + indicator of x = 0, exact at ȳ = 1 and strict at 0, where (1, 0) is stationary for y^ν = 1
--   - generalization: ε^ν ↘ 0 → ε^ν ≥ 0 and ε^ν → 0; reason: monotonicity is not used, every reading of ↘ implies this, and the published Theorem 3.7 states it the same way
--   - encoding: ∂ and dist on ℝ^{m+n}, empty and ∞ at the degenerate inputs → transport to EuclideanSpace ℝ (Fin m ⊕ Fin n), subdiff empty at ±∞, Metric.infEDist; reason: the paper's definitions on pp.12 and 24
--   - encoding: subsequence N ⊂ ℕ, cluster point, ν ∈ {1, 2, …}, convex R̄-valued function → strictly increasing index map, MapClusterPt, ν from 0, convex real epigraph; reason: standard equivalent forms
-- source:
--   Royset, Chen & Eckstrand, Rockafellian Relaxation and Stochastic Optimization under Perturbations, arXiv:2204.04762v4, Theorem 5.2 and display (5.1), pp.24–25

import Mathlib
import Definitions.Def_PerspEpi_SeqEpiConv
import Definitions.Def_WassersteinDRO_ConvexLossP1_IsConvexExt
import Definitions.Def_RockafellianRelax_IsExact
import Definitions.Def_RockafellianRelax_IsStrictlyExact
import Definitions.Def_RockafellianRelax_argmin
import Definitions.Def_RockafellianRelax_Supplement_IsProper
import Definitions.Def_RockafellianRelax_Supplement_jointEuclid
import Definitions.Def_RockafellianRelax_Supplement_subdiff
import Definitions.Def_RockafellianRelax_Supplement_subdiffGraph
import Definitions.Def_RockafellianRelax_Supplement_outerLimit
open Filter Topology

namespace RockafellianRelax.Supplement

/-- **Theorem 5.2 (convergence to first-order optimality condition).** Royset, Chen & Eckstrand, arXiv:2204.04762v4, Theorem 5.2, pp.24–25:
"For the problem of minimizing a proper function φ : ℝⁿ → R̄, suppose that yν → ȳ, εν ↘ 0, and
f : ℝᵐ × ℝⁿ → R̄ is an exact Rockafellian supported by ȳ ∈ ℝᵐ. If the functions
{fν : ℝᵐ × ℝⁿ → R̄, ν ∈ ℕ} satisfy the property LimOut(gph ∂fν) ⊂ gph ∂f (5.1) and (uν, xν) solves
(yν, 0) ∈ ∂fν(u, x) with tolerance εν, i.e., dist((yν, 0), ∂fν(uν, xν)) ≤ εν, then every cluster
point of {(uν, xν), ν ∈ ℕ} satisfies the necessary first-order optimality condition in Theorem 5.1.
Under the additional assumptions that {fν, ν ∈ ℕ} are strictly limit-exact Rockafellians with f
being their limit and each fν being proper, lsc, convex, then (5.1) holds automatically and every
cluster point (û, x̂) of {(uν, xν), ν ∈ ℕ} satisfies û = 0 and x̂ ∈ argmin_x φ(x)."

Conjuncts: (1) under (5.1) and the tolerance condition, `(ȳ, 0) ∈ ∂f(û, x̂)` at every cluster point;
(2) under the additional assumptions (5.1) holds; (3) under the additional assumptions and the
tolerance condition, without assuming (5.1), `û = 0` and `x̂ ∈ argmin φ`.

**Formalization Note.** "Satisfies the condition in Theorem 5.1" is read as `(ȳ, 0) ∈ ∂f(û, x̂)`
(p.24, the paragraph before the theorem). "Strictly limit-exact with f being their limit" is read
as `f` strictly exact, supported by the same `ȳ`, and `fν` epi-converging to `f`. `εν ↘ 0` is
relaxed to `εν ≥ 0 ∧ εν → 0`, as in the published Theorem 3.7. `dist` is Euclidean on `ℝ^{m+n}`
and `⊤` on `∅`, so the tolerance condition forces `∂fν(uν, xν)` to be nonempty. A cluster point is
`MapClusterPt`, and `ν` runs over Lean's `ℕ` from `0`. -/
theorem theorem_5_2 {m n : ℕ} (φ : (Fin n → ℝ) → EReal) (hφ : IsProper φ)
    (f : (Fin m → ℝ) × (Fin n → ℝ) → EReal) (ybar : Fin m → ℝ) (hex : IsExact f φ ybar)
    (F : ℕ → (Fin m → ℝ) × (Fin n → ℝ) → EReal) :
    (∀ (y : ℕ → Fin m → ℝ) (ε : ℕ → ℝ) (z : ℕ → (Fin m → ℝ) × (Fin n → ℝ)),
      Tendsto y atTop (𝓝 ybar) → (∀ ν, 0 ≤ ε ν) → Tendsto ε atTop (𝓝 0) →
      outerLimit (fun ν => subdiffGraph (F ν)) ⊆ subdiffGraph f →
      (∀ ν, Metric.infEDist (jointEuclid (y ν, (0 : Fin n → ℝ)))
        (jointEuclid '' subdiff (F ν) (z ν)) ≤ ENNReal.ofReal (ε ν)) →
      ∀ zhat : (Fin m → ℝ) × (Fin n → ℝ), MapClusterPt zhat atTop z →
        (ybar, (0 : Fin n → ℝ)) ∈ subdiff f zhat) ∧
    (IsStrictlyExact f φ ybar → PerspEpi.SeqEpiConv F f →
      (∀ ν, IsProper (F ν)) → (∀ ν, LowerSemicontinuous (F ν)) →
      (∀ ν, WassersteinDRO.ConvexLossP1.IsConvexExt (F ν)) →
      outerLimit (fun ν => subdiffGraph (F ν)) ⊆ subdiffGraph f ∧
        ∀ (y : ℕ → Fin m → ℝ) (ε : ℕ → ℝ) (z : ℕ → (Fin m → ℝ) × (Fin n → ℝ)),
          Tendsto y atTop (𝓝 ybar) → (∀ ν, 0 ≤ ε ν) → Tendsto ε atTop (𝓝 0) →
          (∀ ν, Metric.infEDist (jointEuclid (y ν, (0 : Fin n → ℝ)))
            (jointEuclid '' subdiff (F ν) (z ν)) ≤ ENNReal.ofReal (ε ν)) →
          ∀ zhat : (Fin m → ℝ) × (Fin n → ℝ), MapClusterPt zhat atTop z →
            zhat.1 = 0 ∧ zhat.2 ∈ argmin φ) := by sorry

end RockafellianRelax.Supplement
