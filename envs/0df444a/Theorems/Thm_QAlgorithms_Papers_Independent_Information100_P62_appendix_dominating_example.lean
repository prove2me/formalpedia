-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P62_appendix_dominating_example
-- name    : QAlgorithms.Papers.Independent.Information100.P62.appendix_dominating_example
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-18T22:01:21.203944+00:00
-- url     : https://prove2.me/theorems/68d718c4-4685-4309-a253-03b1109931e6
-- title:
--   Appendix B.1 unnumbered dominating-algebra example
-- statement:
--   For the channel on $M_4(\mathbb C)$ with $E_0=|0\rangle\langle0|+|1\rangle\langle1|$ and $E_1=|1\rangle\langle2|+|3\rangle\langle3|$,
--   $$A_{\rm dom}(\Phi)\cong M_2(\mathbb C)\oplus\mathbb C.$$
--   This is an explicit channel admitting domination beyond the sufficient families discussed in the main text.
-- source:
--   Transmitting algebras through quantum channels, arXiv:2609.40054v1, PDF p. 60, Appendix B.1 unnumbered dominating-algebra example

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P62

namespace QAlgorithms.Papers.Independent.Information100.P62

noncomputable section

open scoped ComplexConjugate Matrix ComplexOrder

open Finset

attribute [local instance] Classical.propDecidable

variable {I O J K : Type} [Fintype I] [Fintype O] [Fintype J] [Fintype K]

variable [DecidableEq I] [DecidableEq O] [DecidableEq J] [DecidableEq K]

/-- arXiv:2609.40054v1, PDF pp.60, 61, Appendix B.1 unnumbered dominating-algebra example. -/
theorem appendix_dominating_example :
    IsChannel appendixExample ∧ Dominating appendixExample (quantum 2 + quantum 1) := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P62
