-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ringKrullDim_curveNormalisation_le_a06ad3adf3e1
-- name    : P2M_GroundTheory_Heights__Heights_ringKrullDim_curveNormalisation_le_a06ad3adf3e1
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:50:28.46163+00:00
-- url     : https://prove2.me/theorems/960e73d9-98f8-4df3-bd8a-eb52f7b045e1
-- title:
--   P2 M Ground Theory Heights  Heights ring Krull Dim curve Normalisation le a06ad3adf3e1: P2 M Ground Theory Heights  Heights ring Krull Dim curve Normalisation le a06ad3adf3e1
-- statement:
--   The P2 M Ground Theory Heights  Heights ring Krull Dim curve Normalisation le a06ad3adf3e1 construction uses the P2 M Ground Theory Heights  Heights ring Krull Dim curve Normalisation le a06ad3adf3e1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/POrdDeterminesPlace.lean#L19-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/POrdDeterminesPlace.lean#L19-L23

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StOrdDeterminesPlace
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCurveNormalisationFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_POrdDeterminesPlace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial ComplexSets
noncomputable section
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_ringKrullDim_curveNormalisation_le_a06ad3adf3e1 (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) :
    ringKrullDim (curveNormalisation I q) ≤ ringKrullDim (curveLocalRing I q) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ringKrullDim_curveNormalisation_le» := P2M_GroundTheory_Heights__Heights_ringKrullDim_curveNormalisation_le_a06ad3adf3e1
