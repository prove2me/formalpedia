-- Prove2me | Theorems.Thm_SFLOracleLowerBound_Hardness_sfl_oracle_lower_bound
-- name    : SFLOracleLowerBound.Hardness.sfl_oracle_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T02:27:22.3696+00:00
-- url     : https://prove2.me/theorems/5b26cee5-99a7-4aef-b730-5ca3dc8975eb
-- title:
--   Theorem 2 — Value-oracle lower bound for SFL
-- statement:
--   There exists an absolute $\alpha_0>0$ such that every adaptive randomized exact-value oracle algorithm with one uniform polynomial worst-case query bound has the following failure property: for every fixed $p\in(0,1]$ and every size cutoff, some larger SFL instance with a matroid-rank facility cost has
--   $$\Pr[\operatorname{cost}(\sigma)\le\alpha_0\log\log|\mathcal C|\cdot\mathrm{OPT}]<p.$$
--   The constant is chosen before the algorithm, its polynomial, $p$ and the cutoff. Public distances can be arbitrary finite real pseudometric distances. Computation and private randomness are unrestricted, subject to measurability of observable runs.
--
--   Thus no polynomial-query algorithm attains this factor with any fixed positive success probability uniformly over inputs. The same conclusion excludes $o(\log\log|\mathcal C|)$ factors, and hence constant-factor approximation, as stated after Theorem 2. The theorem is unconditional and does not assume a computational complexity separation.
--
--   Differences from the source:
--   - encoding: arbitrary adaptive randomized exact-value algorithms → transcript strategies with real answers and private seeds on arbitrary probability spaces, with measurable observable runs; reason: all oracle dependence occurs through the transcript; measurability makes the stated probabilities well-defined and no support restriction is imposed
--   - encoding: no uniform constant-success guarantee, with asymptotic hard sizes established on p.26 → for every positive p≤1 and every cutoff, a counterexample above the cutoff with at least 16 clients; reason: this expresses the proved unbounded-size content and excludes an artifact of nonpositive small-size logarithms
--   - encoding: one polynomial query bound → one natural-coefficient polynomial evaluated at n+m on positive finite carriers Fin n and Fin m, with the budget required on matroid-rank inputs; reason: every ordinary polynomial bound is dominated by such a polynomial, and relabelling covers all finite nonempty inputs
-- source:
--   Adam N. Elmachtoub, Bento Natura, Meike Neuwohner, Settling the Approximability of Submodular Facility Location, STOC 2027 submission #1249 (October 2026), Theorem 2, pp.2–3; proof p.26; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1249.pdf

import Mathlib
import Definitions.Def_SFLOracleLowerBound_Hardness_Oracle

set_option autoImplicit false

noncomputable section

namespace SFLOracleLowerBound.Hardness

open Classical Finset MeasureTheory
open scoped ENNReal

/-- Theorem 2, pp.2–3; its unbounded-size content is proved on p.26. -/

theorem sfl_oracle_lower_bound : ∃ α₀ : ℝ, 0 < α₀ ∧
    ∀ (A : AlgorithmFamily) (Q : Polynomial ℕ), PolynomialQueryBound A Q →
    ∀ p : ℝ, 0 < p → p ≤ 1 → ∀ cutoff : ℕ,
      ∃ (n m : ℕ) (D : PublicData (Fin n) (Fin m)) (g : Finset (Fin n) → ℝ),
        cutoff < n ∧ 16 ≤ n ∧ 0 < m ∧ IsSFL D ∧ FacilityCost g ∧ MatroidRank g ∧
        successProbability (A n m D) D g (Q.eval (n+m)) (α₀ * Real.log (Real.log n)) < p := by sorry

end SFLOracleLowerBound.Hardness
