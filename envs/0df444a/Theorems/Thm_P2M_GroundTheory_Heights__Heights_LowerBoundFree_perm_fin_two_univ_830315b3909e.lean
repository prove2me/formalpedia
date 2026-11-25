-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_perm_fin_two_univ_830315b3909e
-- name    : P2M_GroundTheory_Heights__Heights_LowerBoundFree_perm_fin_two_univ_830315b3909e
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:27:56.408547+00:00
-- url     : https://prove2.me/theorems/d9defe95-0549-5883-9f74-5799b17616e0
-- title:
--   P2 M Ground Theory Heights  Heights Lower Bound Free perm fin two univ 830315b3909e: P2 M Ground Theory Heights  Heights Lower Bound Free perm fin two univ 830315b3909e
-- statement:
--   The P2 M Ground Theory Heights  Heights Lower Bound Free perm fin two univ 830315b3909e construction uses the P2 M Ground Theory Heights  Heights Lower Bound Free perm fin two univ 830315b3909e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/FrameDefinitions/PermFinTwoUniv.lean#L69-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/FrameDefinitions/PermFinTwoUniv.lean#L69-L70

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_FrameDefinitions_PermFinTwoUniv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open MvPolynomial

theorem P2M_GroundTheory_Heights__Heights_LowerBoundFree_perm_fin_two_univ_830315b3909e : (Finset.univ : Finset (Equiv.Perm (Fin 2))) = {1, Equiv.swap 0 1} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LowerBoundFree».«perm_fin_two_univ» := P2M_GroundTheory_Heights__Heights_LowerBoundFree_perm_fin_two_univ_830315b3909e
