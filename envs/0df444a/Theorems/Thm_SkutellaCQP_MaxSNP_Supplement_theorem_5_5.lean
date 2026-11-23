-- Prove2me | Theorems.Thm_SkutellaCQP_MaxSNP_Supplement_theorem_5_5
-- name    : SkutellaCQP.MaxSNP.Supplement.theorem_5_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T09:52:28.263289+00:00
-- url     : https://prove2.me/theorems/a9ae3e1a-9f9c-4575-b89f-545bddfd312a
-- title:
--   Theorem 5.5 — conditional 1.2752 bound for independent or modified-hyperplane rounding
-- statement:
--   Assume Conjecture 5.3. For positive real processing times and nonnegative weights on two machines without release dates, let a feasible SDP solution have additive error $0\le\delta\le\delta_{55}$, where $q=31399/24623$, $L=\sum_jw_j\min_i p_{ij}$ and $\delta_{55}=(1.2752-q)L/(2q)$. Then independent rounding and modified hyperplane rounding are probability laws, and
--   $$\left(\mathbb E_{\rm independent}\sum_jw_jC_j\le1.2752 Z^*\right)\quad\text{or}\quad\left(\mathbb E_{f_2\text{-hyperplane}}\sum_jw_jC_j\le1.2752 Z^*\right).$$
--   Selecting the smaller of the two computable bounds $Z+c^Ta/2$ and $\rho_1(3c^Ta/4)+\rho_2(Z-3c^Ta/4)$ achieves the same bound. This does not require knowing $Z^*$. The statement also supplies uniform polynomial-time finite fair-coin implementations of the selected law, at any requested accuracy, retaining the exact constant. Zero weights and zero SDP value are included without division by $Z$.
--
--   Differences from the source:
--   - encoding: almost optimal and the strict numerical maximum below 1.2752 → explicit error δ₅₅ using the exact crossing value 31399/24623; reason: the strict slack absorbs near-optimization error without weakening the constant
--   - generalization: one of the two expected-value guarantees → the full disjunction, an explicit upper-bound choice, and uniform finite implementations at every total-variation accuracy; reason: the source guarantee is a direct conjunct; the extra conclusions specify an implementable choice
-- source:
--   Skutella, Convex quadratic and semidefinite programming relaxations in scheduling, J. ACM 48 (2001), DOI 10.1145/375827.375840, p. 29, Theorem 5.5

import Mathlib
import Definitions.Def_SkutellaCQP_MaxSNP_Supplement_SDPAlgorithm

namespace SkutellaCQP.MaxSNP.Supplement

/-- Theorem 5.5, p. 29: both algorithms, their disjunction, a computable selection rule,
and a uniform finite implementation with the exact factor. -/
theorem theorem_5_5 (hc : Conjecture53) :
    (∀ (n : ℕ) (p : Two → Fin n → ℝ) (w : Fin n → ℝ),
      (∀ i j, 0 < p i j) → (∀ j, 0 ≤ w j) →
      ∀ (v : Vectors n) (Z δ : ℝ), 0 ≤ δ → δ ≤ tolerance55 p w →
        AlmostOptimal p w v Z δ →
        IsAssignmentLaw (independentLaw v) ∧ IsAssignmentLaw (modifiedLaw v) ∧
        ((expectedValue p w (independentLaw v) ≤ (797 / 625 : ℝ) * optimum p w) ∨
          (expectedValue p w (modifiedLaw v) ≤ (797 / 625 : ℝ) * optimum p w)) ∧
        expectedValue p w (selectedLaw p w v Z) ≤ (797 / 625 : ℝ) * optimum p w) ∧
    (∃ (A : TwoInput → SDPOutput) (q : Polynomial ℕ) (B : List Bool → List Bool),
      SDPImplementation tolerance55 (fun p w v Z => selectedLaw p w v Z) A q B ∧
      ∀ I k, IsAssignmentLaw (coinLaw q B I k) ∧
        expectedValue I.pr I.wr (coinLaw q B I k) ≤
          (797 / 625 : ℝ) * optimum I.pr I.wr) := by sorry

end SkutellaCQP.MaxSNP.Supplement
