-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_bx_towerPairing
-- name    : ReciprocityTheory.PGsh.bx_towerPairing
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T16:33:37.631922+00:00
-- url     : https://prove2.me/theorems/6afe81c9-d68c-5ef1-9304-63bb772b4853
-- title:
--   PGsh: bx tower Pairing
-- statement:
--   The PGsh construction uses the bx tower Pairing property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ThmAAll.lean#L13-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ThmAAll.lean#L13-L14

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

theorem ReciprocityTheory.PGsh.bx_towerPairing {R₀ : Type*} [CommRing R₀] (B : BX R₀) {p : ℕ} (Tw : ATower R₀ p) : NsetExpInjectiveSurjective B Tw := by sorry
