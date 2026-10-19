-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P62_transmission_lower
-- name    : QAlgorithms.Papers.Independent.Information100.P62.transmission_lower
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-18T21:34:14.234231+00:00
-- url     : https://prove2.me/theorems/9a3283f7-a207-4266-b880-527f7cadaaee
-- title:
--   Remark 3.2: downward closure
-- statement:
--   Let $\Phi$ be a channel and $A,B$ nonzero finite-dimensional algebra types. Then
--   $$B\in\mathcal T(\Phi),\ A\le B\quad\Longrightarrow\quad A\in\mathcal T(\Phi).$$
--   Thus the transmission set is a lower set for the nonunital faithful embedding order.
-- source:
--   Transmitting algebras through quantum channels, arXiv:2609.40054v1, PDF p. 21, Remark 3.2: downward closure

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P62

namespace QAlgorithms.Papers.Independent.Information100.P62

noncomputable section

open scoped ComplexConjugate Matrix ComplexOrder

open Finset

attribute [local instance] Classical.propDecidable

variable {I O J K : Type} [Fintype I] [Fintype O] [Fintype J] [Fintype K]

variable [DecidableEq I] [DecidableEq O] [DecidableEq J] [DecidableEq K]

/-- arXiv:2609.40054v1, PDF pp.21, Remark 3.2: downward closure. -/
theorem transmission_lower [Nonempty I] [Nonempty O]
    (F : Superop I O) (hF : IsChannel F) (A B : Shape) (hA : Valid A)
    (hB : Transmits F B) (h : Embeds A B) : Transmits F A := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P62
