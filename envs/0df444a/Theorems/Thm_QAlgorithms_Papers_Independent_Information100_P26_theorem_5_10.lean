-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P26_theorem_5_10
-- name    : QAlgorithms.Papers.Independent.Information100.P26.theorem_5_10
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T10:42:25.987632+00:00
-- url     : https://prove2.me/theorems/bfe2b08d-a9c7-40c0-92c8-3d4a98bfd51d
-- title:
--   Theorem 5.10: an MTD neighborhood within compatible unital channels
-- statement:
--   For every commutative unital $C^*$-subalgebra $A\subseteq M_d$, $d\ge1$, there exists $\varepsilon>0$ such that every unital channel $\tau$ with $A\subseteq\operatorname{Fix}(\tau)\cap\operatorname{Range}(\tau)'$ satisfies
--   $$\|E_A-\tau\|_{\rm HS}<\varepsilon\quad\Longrightarrow\quad\tau\in\operatorname{MTD}(d).$$
--   The radius is chosen before $\tau$. Both compatibility conditions are retained, and $A$ may be non-diagonal.
-- source:
--   A complete characterization of eventually entanglement breaking unital quantum channels, arXiv:2609.24168v1, PDF p. 20, Theorem 5.10

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P26

noncomputable section

open scoped BigOperators ComplexConjugate Matrix ComplexOrder Matrix.Norms.Frobenius

open MeasureTheory Filter Set

namespace QAlgorithms.Papers.Independent.Information100.P26

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance] QAlgorithms.Papers.Independent.Information100.P26.unitaryMeasurable

/-- arXiv:2609.24168v1, Theorem 5.10, PDF pp.20. -/
theorem theorem_5_10 {d : ℕ} (hd : 0 < d) (A : Submodule ℂ (Mat d))
    (hA : CStar A) (hcomm : Commutative A) :
    ∃ e : ℝ, 0 < e ∧ ∀ t : Map d, UnitalChannel t → Compatible A t →
      hsNorm (expectation A - t) < e → MTD t := by sorry

end QAlgorithms.Papers.Independent.Information100.P26

end
