-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P62_graph_characterization
-- name    : QAlgorithms.Papers.Independent.Information100.P62.graph_characterization
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T21:38:10.295548+00:00
-- url     : https://prove2.me/theorems/01d08d5c-0529-4a04-9429-7af45aae40ed
-- title:
--   Unnumbered graph characterization (3.10)
-- statement:
--   Let $A=\bigoplus_kM_{d_k}(\mathbb C)$ be represented without multiplicities, with pinching channel $P_A$. For any channel $\Phi$,
--   $$A\in\mathcal T(\Phi)\iff S_{P_A}\longrightarrow S_\Phi.$$
--   Here $S_{P_A}=\bigoplus_k\mathbb CI_{d_k}$. This is an exact graph characterization of transmission.
-- source:
--   Transmitting algebras through quantum channels, arXiv:2609.40054v1, PDF p. 25, Unnumbered graph characterization (3.10)

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P62

namespace QAlgorithms.Papers.Independent.Information100.P62

noncomputable section

open scoped ComplexConjugate Matrix ComplexOrder

open Finset

attribute [local instance] Classical.propDecidable

variable {I O J K : Type} [Fintype I] [Fintype O] [Fintype J] [Fintype K]

variable [DecidableEq I] [DecidableEq O] [DecidableEq J] [DecidableEq K]

/-- arXiv:2609.40054v1, PDF pp.25, Unnumbered graph characterization (3.10). -/
theorem graph_characterization [Nonempty I] [Nonempty O]
    (F : Superop I O) (hF : IsChannel F) (A : Shape) (hA : Valid A) :
    Transmits F A ↔ GraphHom (pinchingSystem A) (graph F) := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P62
