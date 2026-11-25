-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_one_le_ringKrullDim_localRingAt_sliceIdeal_93fe90c97dbc
-- name    : P2M_GroundTheory_Heights__Heights_one_le_ringKrullDim_localRingAt_sliceIdeal_93fe90c97dbc
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:50:32.126513+00:00
-- url     : https://prove2.me/theorems/aa50be64-fb5e-4f37-b5d0-1b3bfc0acf69
-- title:
--   P2 M Ground Theory Heights  Heights one le ring Krull Dim local Ring At slice Ideal 93fe90c97dbc: P2 M Ground Theory Heights  Heights one le ring Krull Dim local Ring At slice Ideal 93fe90c97dbc
-- statement:
--   The P2 M Ground Theory Heights  Heights one le ring Krull Dim local Ring At slice Ideal 93fe90c97dbc construction uses the P2 M Ground Theory Heights  Heights one le ring Krull Dim local Ring At slice Ideal 93fe90c97dbc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSliceLocalDimGeneral.lean#L40-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSliceLocalDimGeneral.lean#L40-L77

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceLocalDimGeneral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceLocalDimUpperZariski
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLocalDimDomain
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSliceReducedAway
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSliceLocalDimGeneral
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
open MvPolynomial Matrix ComplexSets
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_one_le_ringKrullDim_localRingAt_sliceIdeal_93fe90c97dbc {n d : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ))
    (L : Matrix (Fin d) (Fin n) ℂ) (q : Fin n → ℂ)
    (hdim : ringKrullDim (localRingAt J q) = (d + 1 : ℕ)) :
    ((1 : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (localRingAt (sliceIdeal J L q) q) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«one_le_ringKrullDim_localRingAt_sliceIdeal» := P2M_GroundTheory_Heights__Heights_one_le_ringKrullDim_localRingAt_sliceIdeal_93fe90c97dbc
