-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P14_order_axioms_and_comparison
-- name    : QAlgorithms.Papers.Independent.Advance50.P14.order_axioms_and_comparison
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T10:21:52.637656+00:00
-- url     : https://prove2.me/theorems/4297389e-0a08-4dcf-ab4a-86266ca1181d
-- title:
--   Section VI unnumbered: axioms 1–4 and comparison
-- statement:
--   All systems are finite-dimensional complex multipartite systems with at least two parties and positive local dimensions. Every state is positive semidefinite with trace one. Separability means a convex mixture of products across all parties. Logarithms are base two, and the trace norm has no factor of one half. Write $X\prec Y$ for asymptotic conversion by CPTP maps with uniformly vanishing global-robustness leakage and vanishing full trace-norm error. Finite weighted products are realized by actual integer component counts divided by the blocklength tending to their nonnegative weights; a zero weight means exactly zero copies. The following laws hold:
--
--   $$X\prec X,\qquad (X\prec Y\ \land\ Y\prec Z)\Rightarrow X\prec Z,\qquad X\prec Y\Rightarrow tX\prec tY\quad(t>0),$$
--
--   $$X\prec(tX,(1-t)X)\prec X\quad(0\le t\le1),\qquad X\prec Y\ \lor\ Y\prec X.$$
--
--   Reflexivity, transitivity and scaling apply to finite weighted products. Comparison includes two-fold scaled products. Scaling refers to asymptotic copy rates, not fractional powers of a density matrix. These are axioms 1–4 and comparison; tensor consistency is left open.
-- source:
--   A reversible theory of entanglement and its relation to the second law, arXiv:0710.5827v3, PDF p. 17, Section VI unnumbered: axioms 1–4 and comparison

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P14

noncomputable section

open Filter

open QAlgorithms.Papers.Independent.Claimed50.P33 (RegisterBasis)

open scoped Matrix ComplexOrder ENNReal NNReal

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Advance50.P14

/-- PDF pp.17–19: axioms 1–4 (reflexivity, transitivity, positive scaling,
splitting/recombination) and comparison, including the two-fold scaled products.
The y in axiom 4's printed interval is corrected to its fraction t.
Zero weights have zero copies, and both endpoints are retained. Axiom 6 is
not included: the paper explicitly leaves its unconditional validity open. -/
theorem order_axioms_and_comparison :
    (∀ {m q : ℕ} (X : WeightedFamily m q), WeightedConverts X X) ∧
    (∀ {m p q r : ℕ} (X : WeightedFamily m p) (Y : WeightedFamily m q)
      (Z : WeightedFamily m r), WeightedConverts X Y → WeightedConverts Y Z →
      WeightedConverts X Z) ∧
    (∀ {m p q : ℕ} (X : WeightedFamily m p) (Y : WeightedFamily m q)
      (t : ℝ≥0), 0 < t → WeightedConverts X Y →
      WeightedConverts (scaleFamily t X) (scaleFamily t Y)) ∧
    (∀ {m : ℕ} (X : PhysicalState m) (t : ℝ≥0), t ≤ 1 →
      WeightedConverts (singleFamily X 1) (pairFamily X X t (1 - t)) ∧
      WeightedConverts (pairFamily X X t (1 - t)) (singleFamily X 1)) ∧
    (∀ {m l : ℕ} (A : MultipartiteRegister m) (B : MultipartiteRegister l) (rho : PartyOperator A)
      (sigma : PartyOperator B), IsDensityMatrix rho → IsDensityMatrix sigma →
      AsymptoticConverts A rho B sigma ∨ AsymptoticConverts B sigma A rho) ∧
    (∀ {m : ℕ} (X Y Z W : PhysicalState m) (t : ℝ≥0), t ≤ 1 →
      WeightedConverts (pairFamily X Y t (1 - t)) (pairFamily Z W t (1 - t)) ∨
      WeightedConverts (pairFamily Z W t (1 - t)) (pairFamily X Y t (1 - t))) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P14

end
