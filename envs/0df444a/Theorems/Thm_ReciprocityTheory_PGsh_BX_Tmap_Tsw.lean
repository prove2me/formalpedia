-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_BX_Tmap_Tsw
-- name    : ReciprocityTheory.PGsh.BX.Tmap_Tsw
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:05:28.67296+00:00
-- url     : https://prove2.me/theorems/871ccb25-7c81-41d3-bb45-b3dd0ce43128
-- title:
--   BX: Tmap Tsw
-- statement:
--   The BX construction uses the Tmap Tsw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/TotalFibreMapTotalFibreNsmulSnd.lean#L45-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/TotalFibreMapTotalFibreNsmulSnd.lean#L45-L47

import Definitions.Def_ReciprocityTheory_DualLattices_NsmulTensorEqZero
import Definitions.Def_ReciprocityTheory_DualLattices_SmKerSurj
import Definitions.Def_ReciprocityTheory_DualLattices_TangentPairingStatement
import Definitions.Def_ReciprocityTheory_DualLattices_TotalFibreMapTotalFibreNsmulSnd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct
open ReciprocityTheory ReciprocityTheory.PGsh
universe u
variable {R₀ : Type u} [CommRing R₀]
open ReciprocityTheory.PGsh.BX
variable (B : BX R₀)

theorem ReciprocityTheory.PGsh.BX.Tmap_Tsw {R S : LAlg R₀} (f : LHom R S) (t : B.Tot R) :
    B.Tmap f (B.Tsw t) = B.Tsw (B.Tmap f t) := by sorry
