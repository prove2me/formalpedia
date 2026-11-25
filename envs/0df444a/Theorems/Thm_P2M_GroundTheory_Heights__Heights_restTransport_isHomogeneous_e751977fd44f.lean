-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_restTransport_isHomogeneous_e751977fd44f
-- name    : P2M_GroundTheory_Heights__Heights_restTransport_isHomogeneous_e751977fd44f
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:57:01.220794+00:00
-- url     : https://prove2.me/theorems/548ffcfe-ac31-4d5b-8265-89da59d915b2
-- title:
--   P2 M Ground Theory Heights  Heights rest Transport is Homogeneous e751977fd44f: P2 M Ground Theory Heights  Heights rest Transport is Homogeneous e751977fd44f
-- statement:
--   The P2 M Ground Theory Heights  Heights rest Transport is Homogeneous e751977fd44f construction uses the P2 M Ground Theory Heights  Heights rest Transport is Homogeneous e751977fd44f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PRestCutIKillsIdeal.lean#L13-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PRestCutIKillsIdeal.lean#L13-L17

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsRest
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PRestCutIKillsIdeal
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
open MvPolynomial

theorem P2M_GroundTheory_Heights__Heights_restTransport_isHomogeneous_e751977fd44f (f j k N : ℕ) (e : Fin N ≃ Fin j ⊕ Fin k)
    {A : RestTerms.RootRing f N} {d : ℕ} (hA : A.IsHomogeneous d) :
    (restTransport f j k N e A).IsHomogeneous d := by sorry

alias «GroundTheory».«Heights₂».«Heights».«restTransport_isHomogeneous» := P2M_GroundTheory_Heights__Heights_restTransport_isHomogeneous_e751977fd44f
