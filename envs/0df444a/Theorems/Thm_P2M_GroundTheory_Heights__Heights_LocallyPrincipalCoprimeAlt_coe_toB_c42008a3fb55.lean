-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LocallyPrincipalCoprimeAlt_coe_toB_c42008a3fb55
-- name    : P2M_GroundTheory_Heights__Heights_LocallyPrincipalCoprimeAlt_coe_toB_c42008a3fb55
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:26:09.934331+00:00
-- url     : https://prove2.me/theorems/532f41af-dcdd-49d8-a42e-64b47739673f
-- title:
--   P2 M Ground Theory Heights  Heights Locally Principal Coprime Alt coe to B c42008a3fb55: P2 M Ground Theory Heights  Heights Locally Principal Coprime Alt coe to B c42008a3fb55
-- statement:
--   The P2 M Ground Theory Heights  Heights Locally Principal Coprime Alt coe to B c42008a3fb55 construction uses the P2 M Ground Theory Heights  Heights Locally Principal Coprime Alt coe to B c42008a3fb55 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PLocallyPrincipalCoprime.lean#L102-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PLocallyPrincipalCoprime.lean#L102-L103

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLocallyPrincipalCoprime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLocallyPrincipalCoprime
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
open GroundTheory.Heights₂.Heights.LocallyPrincipalCoprimeAlt
variable {L : Type} [Field L]

theorem P2M_GroundTheory_Heights__Heights_LocallyPrincipalCoprimeAlt_coe_toB_c42008a3fb55 {B : Subring L} {x : L} (h : x ∈ B) : (toB B x : L) = x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LocallyPrincipalCoprimeAlt».«coe_toB» := P2M_GroundTheory_Heights__Heights_LocallyPrincipalCoprimeAlt_coe_toB_c42008a3fb55
