-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_one_le_ringKrullDim_of_relevant_82aa6fd299a7
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_one_le_ringKrullDim_of_relevant_82aa6fd299a7
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T07:10:16.180122+00:00
-- url     : https://prove2.me/theorems/d0d4a3d0-e840-448c-ad08-95e85c63e44a
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman one le ring Krull Dim of relevant 82aa6fd299a7: P2 M Ground Theory Heights  Heights Kleiman one le ring Krull Dim of relevant 82aa6fd299a7
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman one le ring Krull Dim of relevant 82aa6fd299a7 construction uses the P2 M Ground Theory Heights  Heights Kleiman one le ring Krull Dim of relevant 82aa6fd299a7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSnapper.lean#L93-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSnapper.lean#L93-L113

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
variable {k : Type u} [Field k] {N : ℕ}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_one_le_ringKrullDim_of_relevant_82aa6fd299a7 (pp : Ideal (Poly k N)) [pp.IsPrime]
    (hh : ∀ f ∈ pp, ∀ d : ℕ, homogeneousComponent d f ∈ pp) (hrel : ∃ i, (X i : Poly k N) ∉ pp) :
    1 ≤ ringKrullDim (Poly k N ⧸ pp) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«one_le_ringKrullDim_of_relevant» := P2M_GroundTheory_Heights__Heights_Kleiman_one_le_ringKrullDim_of_relevant_82aa6fd299a7
