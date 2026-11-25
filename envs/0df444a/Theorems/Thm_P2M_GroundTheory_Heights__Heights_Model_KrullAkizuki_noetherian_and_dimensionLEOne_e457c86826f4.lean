-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_KrullAkizuki_noetherian_and_dimensionLEOne_e457c86826f4
-- name    : P2M_GroundTheory_Heights__Heights_Model_KrullAkizuki_noetherian_and_dimensionLEOne_e457c86826f4
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:29:11.431127+00:00
-- url     : https://prove2.me/theorems/736795df-0af1-482c-9bd7-60b0d289395d
-- title:
--   P2 M Ground Theory Heights  Heights Model Krull Akizuki noetherian and dimension LEOne e457c86826f4: P2 M Ground Theory Heights  Heights Model Krull Akizuki noetherian and dimension LEOne e457c86826f4
-- statement:
--   The P2 M Ground Theory Heights  Heights Model Krull Akizuki noetherian and dimension LEOne e457c86826f4 construction uses the P2 M Ground Theory Heights  Heights Model Krull Akizuki noetherian and dimension LEOne e457c86826f4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PKrullAkizuki.lean#L10-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PKrullAkizuki.lean#L10-L48

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsKrullAkizuki
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PKrullAkizuki
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
open GroundTheory.Heights₂.Heights.Model.KrullAkizuki

theorem P2M_GroundTheory_Heights__Heights_Model_KrullAkizuki_noetherian_and_dimensionLEOne_e457c86826f4
    {R : Type} [CommRing R] [IsDomain R]
    {K : Type} [Field K] [Algebra R K] [IsFractionRing R K]
    {L : Type} [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra R L]
    [IsScalarTower R K L] (S : Subalgebra R L)
    (h : ∀ b : R, b ≠ 0 → IsFiniteLength R (S ⧸ Ideal.span {algebraMap R S b})) :
    IsNoetherianRing S ∧ Ring.DimensionLEOne S := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«KrullAkizuki».«noetherian_and_dimensionLEOne» := P2M_GroundTheory_Heights__Heights_Model_KrullAkizuki_noetherian_and_dimensionLEOne_e457c86826f4
