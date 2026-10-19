-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P26_corollary_5_13
-- name    : QAlgorithms.Papers.Independent.Information100.P26.corollary_5_13
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T10:43:29.563774+00:00
-- url     : https://prove2.me/theorems/aaa5795b-ef78-4f80-a655-1a0fb1799557
-- title:
--   Corollary 5.13: an MTD neighborhood for 2-copositive channels fixing an algebra
-- statement:
--   For each commutative unital $C^*$-subalgebra $A\subseteq M_d$, $d\ge1$, there is $\varepsilon>0$ such that every unital 2-copositive channel $\tau$ fixing $A$ pointwise satisfies
--   $$\|E_A-\tau\|_{\rm HS}<\varepsilon\quad\Longrightarrow\quad\tau\in\operatorname{MTD}(d).$$
--   The radius is uniform over these channels. No range-commutation hypothesis is added: that property is a conclusion of Theorem 5.12.
-- source:
--   A complete characterization of eventually entanglement breaking unital quantum channels, arXiv:2609.24168v1, PDF p. 21, Corollary 5.13

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P26

noncomputable section

open scoped BigOperators ComplexConjugate Matrix ComplexOrder Matrix.Norms.Frobenius

open MeasureTheory Filter Set

namespace QAlgorithms.Papers.Independent.Information100.P26

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance] QAlgorithms.Papers.Independent.Information100.P26.unitaryMeasurable

/-- arXiv:2609.24168v1, Corollary 5.13, PDF pp.21. -/
theorem corollary_5_13 {d : ℕ} (hd : 0 < d) (A : Submodule ℂ (Mat d))
    (hA : CStar A) (hcomm : Commutative A) :
    ∃ e : ℝ, 0 < e ∧ ∀ t : Map d, UnitalChannel t → TwoCopositive t → Fixes t A →
      hsNorm (expectation A - t) < e → MTD t := by sorry

end QAlgorithms.Papers.Independent.Information100.P26

end
