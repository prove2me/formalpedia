-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_pieceChar_of_irrelevant_74e81aeef1ed
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_pieceChar_of_irrelevant_74e81aeef1ed
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T07:09:52.532551+00:00
-- url     : https://prove2.me/theorems/30c435a3-6aba-5e25-a485-ec16e852a91c
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman piece Char of irrelevant 74e81aeef1ed: P2 M Ground Theory Heights  Heights Kleiman piece Char of irrelevant 74e81aeef1ed
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman piece Char of irrelevant 74e81aeef1ed construction uses the P2 M Ground Theory Heights  Heights Kleiman piece Char of irrelevant 74e81aeef1ed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSnapper.lean#L61-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSnapper.lean#L61-L65

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperDiffPolySt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperDevissageSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperHyperplaneSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperSectionSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapper
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u v w
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_pieceChar_of_irrelevant_74e81aeef1ed (pp : Ideal (Poly k N)) (hpp : ∀ i, (X i : Poly k N) ∈ pp) (a : ℤ) {t : ℕ}
    (L : Fin t → LineBundle k x) (n : Fin t → ℕ) (c : ℤ) : pieceChar k pp a L n c = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«pieceChar_of_irrelevant» := P2M_GroundTheory_Heights__Heights_Kleiman_pieceChar_of_irrelevant_74e81aeef1ed
