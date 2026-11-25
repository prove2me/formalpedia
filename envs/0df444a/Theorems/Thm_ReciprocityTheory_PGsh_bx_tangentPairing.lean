-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_bx_tangentPairing
-- name    : ReciprocityTheory.PGsh.bx_tangentPairing
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T16:40:30.504066+00:00
-- url     : https://prove2.me/theorems/4e0278bf-f741-522b-9d1e-060a6c44a9af
-- title:
--   PGsh: bx tangent Pairing
-- statement:
--   The PGsh construction uses the bx tangent Pairing property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ThmAAll.lean#L11-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ThmAAll.lean#L11-L11

import Definitions.Def_ReciprocityTheory_DualLattices_IsPairingValueAddRight
import Definitions.Def_ReciprocityTheory_DualLattices_HeightFunctionalStatementOfPairingProperties
import Definitions.Def_ReciprocityTheory_DualLattices_TangentPairingStatementOfHeightFunctional
import Definitions.Def_ReciprocityTheory_DualLattices_ThmAFull
import Definitions.Def_ReciprocityTheory_DualLattices_AinfTower
import Definitions.Def_ReciprocityTheory_DualLattices_ThmAAll
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.PGsh

theorem ReciprocityTheory.PGsh.bx_tangentPairing {R₀ : Type*} [CommRing R₀] (B : BX R₀) : TangentPairingStatement B := by sorry
