-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_pairingProperties
-- name    : ReciprocityTheory.PGsh.pairingProperties
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:33:44.001193+00:00
-- url     : https://prove2.me/theorems/05d0cc42-cb19-42ad-aab8-b2c3c8c93af5
-- title:
--   PGsh: pairing Properties
-- statement:
--   The PGsh construction uses the pairing Properties property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/IsPairingValueAddRight.lean#L303-L311
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/IsPairingValueAddRight.lean#L303-L311

import Definitions.Def_ReciprocityTheory_DualLattices_SeriesState
import Definitions.Def_ReciprocityTheory_DualLattices_InstAddCommMonoidFibreFst
import Definitions.Def_ReciprocityTheory_DualLattices_NsmulFstAddSnd
import Definitions.Def_ReciprocityTheory_DualLattices_IsPairingValueAddRight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.PGsh
universe u
variable {R₀ : Type u} [CommRing R₀]

theorem ReciprocityTheory.PGsh.pairingProperties (B : BX R₀) : PairingPropertiesStatement B := by sorry
