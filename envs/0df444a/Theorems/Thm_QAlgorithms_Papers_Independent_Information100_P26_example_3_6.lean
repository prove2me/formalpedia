-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P26_example_3_6
-- name    : QAlgorithms.Papers.Independent.Information100.P26.example_3_6
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T10:49:37.438524+00:00
-- url     : https://prove2.me/theorems/4dce3f7e-ef50-4a59-b466-ca9b635a3f43
-- title:
--   Example 3.6: independent product pairs do not suffice without a Kraus condition
-- statement:
--   In $\mathbb C^2$, let $u=(e_1+e_2)/\sqrt2$ and $v=(e_1-e_2)/\sqrt2$. Set $A_1=|e_1\rangle\langle e_1|/\sqrt2$, $A_2=|e_2\rangle\langle u|/\sqrt2$, $A_3=|u\rangle\langle e_2|/\sqrt2$, and $A_4=|v\rangle\langle v|/\sqrt2$. These are rank-one and complex-linearly independent, and $\sum_kA_kA_k^*=\sum_kA_k^*A_k=I_2$. For their constructed channel,
--   $$\tau=\sum_{k=1}^4\operatorname{Ad}_{A_k}\in\operatorname{UEBTP}(2),\qquad\operatorname{CR}(\tau)=4,\qquad\tau\text{ is not extreme}.$$
--   Nevertheless the four pairs $A_kA_k^*\oplus A_k^*A_k$ are real-linearly independent. This exhibits the necessity of the extra Kraus-space condition in Corollary 3.5.
-- source:
--   A complete characterization of eventually entanglement breaking unital quantum channels, arXiv:2609.24168v1, PDF p. 11, Example 3.6

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P26

noncomputable section

open scoped BigOperators ComplexConjugate Matrix ComplexOrder Matrix.Norms.Frobenius

open MeasureTheory Filter Set

namespace QAlgorithms.Papers.Independent.Information100.P26

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance] QAlgorithms.Papers.Independent.Information100.P26.unitaryMeasurable

/-- arXiv:2609.24168v1, Example 3.6, PDF pp.11. -/
theorem example_3_6  :
    (∀ k : Fin 4, (exampleOperators k).rank = 1) ∧
    LinearIndependent ℂ exampleOperators ∧
    (∑ k : Fin 4, (exampleOperators k) * (exampleOperators k)ᴴ) = (1 : Mat 2) ∧
    (∑ k : Fin 4, (exampleOperators k)ᴴ * (exampleOperators k)) = (1 : Mat 2) ∧
    (∑ k : Fin 4, ad (exampleOperators k)) ∈ UEBTP 2 ∧
    choiRank (∑ k : Fin 4, ad (exampleOperators k)) = 4 ∧
    ¬ Extreme (∑ k : Fin 4, ad (exampleOperators k)) ∧
    LinearIndependent ℝ (fun k : Fin 4 => products (exampleOperators k)) := by sorry

end QAlgorithms.Papers.Independent.Information100.P26

end
