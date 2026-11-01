-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P95_input_output_reshaping
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P95.input_output_reshaping
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T08:44:43.585172+00:00
-- url     : https://prove2.me/theorems/9dd7207d-1586-402a-958c-65eea6fc38ce
-- title:
--   Moving an input factor to the output
-- statement:
--   Let $A_1,A_2,B$ be finite orthonormal basis index sets, and let $T:\mathcal H_{A_2}\otimes\mathcal H_{A_1}\to\mathcal H_B$ be an isometry. Define $\widetilde T:\mathcal H_{A_1}\to\mathcal H_B\otimes\mathcal H_{A_2}$ by $\widetilde T_{(b,a_2),a_1}=T_{b,(a_2,a_1)}$, with no conjugation. Then
--
--   $$\widetilde T^\dagger\widetilde T=|A_2|I_{A_1}.$$
--
--   This identity justifies reinterpreting input legs as output legs, with the displayed scalar normalization. It also holds when $A_2$ is empty, when both sides vanish.
-- source:
--   Holographic quantum error-correcting codes: Toy models for the bulk/boundary correspondence, arXiv:1503.06237v2, PDF p. 7, §2, moving an input factor to output (2.4)–(2.5)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P95

namespace QAlgorithms.Papers.Independent.Intakenext100.P95

open scoped Matrix ComplexConjugate

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- PDF pp.6–7, (2.4)–(2.5): reshuffling without conjugation gives the scalar
card(A2), including the harmless empty-A2 case. -/
theorem input_output_reshaping {A1 A2 B : Type*}
    [Fintype A1] [Fintype A2] [Fintype B] [DecidableEq A1] [DecidableEq A2]
    (T : Matrix B (A2 × A1) ℂ) (hT : Tᴴ * T = 1) :
    (moveInput T)ᴴ * moveInput T = (Fintype.card A2 : ℂ) • 1 := by sorry

end

end QAlgorithms.Papers.Independent.Intakenext100.P95
