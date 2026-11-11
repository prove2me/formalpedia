-- Prove2me | Theorems.Thm_SingleCopyMoments_Adaptive_barrier_replacement
-- name    : SingleCopyMoments.Adaptive.barrier_replacement
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T09:49:43.507604+00:00
-- url     : https://prove2.me/theorems/fea7a42b-c57d-4188-8ffb-b068ede03f4e
-- title:
--   Lemma 39 — Uniform barrier replacement
-- statement:
--   Fix $r\ge2$ and $0<\alpha\le1/100$ for the spectral path and cutoff. For a budget function $T(d)$ satisfying $T(d)\log(d+T(d)+1)=o(d)$, there is $c_r>0$ such that eventually, uniformly in $\theta\in[0,\pi/r]$, every frozen history $H$ of length at most $T(d)$, and every deleted subset $J$,
--
--   $$|Z_\theta(H)-\widetilde Z_\theta(H)|+|\partial_\theta Z_\theta(H)-\partial_\theta\widetilde Z_\theta(H)|+|B'_\theta|\le e^{-c_rd},$$
--   $$|\partial_\theta\log Z_\theta(H)-\partial_\theta\log\widetilde Z_\theta(H)|\le e^{-c_rd},$$
--   $$\left|\frac{\widetilde Z_\theta(H\setminus J)}{\widetilde Z_\theta(H)}-\frac{Z_\theta(H\setminus J)}{Z_\theta(H)}\right|\le e^{-c_rd}.$$
--
--   The physical and auxiliary integrands are integrable, the derivatives exist, and all normalizers in these expressions are positive, including after deleting factors. The other projectors remain frozen when indices are removed. The auxiliary expectation does not define a physical state ensemble.
--
--   Differences from the source:
--   - encoding: finite-dimensional states, measurable experiments, and their expectations → complex Fin d matrices, explicit Born/product measures, and normalized measurable operations; reason: the coordinate and measure conventions preserve every positive dimension and arbitrary rank; probability and integrability assertions are conclusions, not extra premises
--   - encoding: o(d), sufficiently large d, and well-defined logarithmic derivatives → a quantified budget limit, one eventual dimension threshold uniform over all frozen histories, integrability, differentiability, and positive denominators; reason: every error term and ratio is retained and no total-operation default supplies a bound
--   - encoding: the fixed sufficiently small prior parameter → 0<alpha<=1/100 from the prior construction; reason: the proof of this lemma uses the initial prior bound, before the further smallness choice (7.44)
-- source:
--   Zhenhuan Liu, STOC 2027 submission #41 (October 2026), Lemma 39, (7.36)–(7.38), printed p. 43 (PDF p. 45); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/41.pdf; PDF SHA-256 f19fd65f41a444a79243fa55aab5dfca3db6adb571b06acff78ee49932174fa9.

import Definitions.Def_SingleCopyMoments_Adaptive_Records

open MeasureTheory Filter
open scoped Topology

namespace SingleCopyMoments.Adaptive

/-- Lemma 39, printed pp.43–44 (PDF pp.45–46), all (7.36)–(7.38) and positivity. -/
theorem barrier_replacement (r : ℕ) (hr : 2 ≤ r) (α : ℝ) (hα : 0 < α)
    (hα₁ : α ≤ 1/100) (T : ℕ → ℕ) (hT : SublinearBudget T) :
    ∃ c > 0, ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → 0 < d →
      ∀ N : ℕ, N ≤ T d → ∀ H : FrozenHistory d N, Frozen H →
      ∀ θ ∈ Set.Icc (0 : ℝ) (Real.pi/r),
      (∀ I : Finset (Fin N),
        Integrable (likelihood α θ H I) (gaussian d r) ∧
        Integrable (fun g => cutoff (radial α θ g) * likelihood α θ H I g) (gaussian d r) ∧
        0 < physicalZ r α θ H I ∧ 0 < auxiliaryZ r α θ H I) ∧
      DifferentiableAt ℝ (fun u => physicalZ r α u H Finset.univ) θ ∧
      DifferentiableAt ℝ (fun u => auxiliaryZ r α u H Finset.univ) θ ∧
      DifferentiableAt ℝ (normalizer d r α) θ ∧
      |physicalZ r α θ H Finset.univ - auxiliaryZ r α θ H Finset.univ| +
        |deriv (fun u => physicalZ r α u H Finset.univ) θ -
          deriv (fun u => auxiliaryZ r α u H Finset.univ) θ| +
        |deriv (normalizer d r α) θ| ≤ Real.exp (-c*d) ∧
      |deriv (fun u => Real.log (physicalZ r α u H Finset.univ)) θ -
        deriv (fun u => Real.log (auxiliaryZ r α u H Finset.univ)) θ| ≤ Real.exp (-c*d) ∧
      (∀ J : Finset (Fin N),
        |auxiliaryZ r α θ H (Finset.univ \ J) / auxiliaryZ r α θ H Finset.univ -
          physicalZ r α θ H (Finset.univ \ J) / physicalZ r α θ H Finset.univ| ≤
            Real.exp (-c*d)) := by sorry

end SingleCopyMoments.Adaptive
