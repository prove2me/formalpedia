-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_BX_Tmap_Tsmul
-- name    : ReciprocityTheory.PGsh.BX.Tmap_Tsmul
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:05:32.50547+00:00
-- url     : https://prove2.me/theorems/63338ab0-442e-4186-a4cc-96879c6341b1
-- title:
--   BX: Tmap Tsmul
-- statement:
--   The BX construction uses the Tmap Tsmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/TotalFibreMapTotalFibreNsmulSnd.lean#L87-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/TotalFibreMapTotalFibreNsmulSnd.lean#L87-L90

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

theorem ReciprocityTheory.PGsh.BX.Tmap_Tsmul {R S : LAlg R₀} (f : LHom R S) (l : (R : Type u)ˣ) (t : B.Tot R) :
    B.Tmap f (B.Tsmul l t) =
      B.Tsmul (Units.map (f.1 : (R : Type u) →* (S : Type u)) l) (B.Tmap f t) := by sorry
