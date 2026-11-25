-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_BX_totalFibreMap_totalFibreNsmulSnd
-- name    : ReciprocityTheory.PGsh.BX.totalFibreMap_totalFibreNsmulSnd
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:06:08.070054+00:00
-- url     : https://prove2.me/theorems/cd5111e9-f13e-50a0-aae7-8290016bfd58
-- title:
--   BX: total Fibre Map total Fibre Nsmul Snd
-- statement:
--   The BX construction uses the total Fibre Map total Fibre Nsmul Snd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/TotalFibreMapTotalFibreNsmulSnd.lean#L80-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/TotalFibreMapTotalFibreNsmulSnd.lean#L80-L82

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

theorem ReciprocityTheory.PGsh.BX.totalFibreMap_totalFibreNsmulSnd {R S : LAlg R₀} (f : LHom R S) (N : ℕ) (t : B.Tot R) :
    B.Tmap f (B.totalFibreNsmulSnd N t) = B.totalFibreNsmulSnd N (B.Tmap f t) := by sorry
