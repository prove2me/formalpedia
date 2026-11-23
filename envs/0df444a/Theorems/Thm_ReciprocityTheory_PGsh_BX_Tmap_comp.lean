-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_BX_Tmap_comp
-- name    : ReciprocityTheory.PGsh.BX.Tmap_comp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:16:34.148402+00:00
-- url     : https://prove2.me/theorems/95cf16ea-9759-4028-916f-3d7eb5c8e673
-- title:
--   BX: Tmap comp
-- statement:
--   The BX construction uses the Tmap comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/TotalFibreMapTotalFibreNsmulSnd.lean#L39-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/TotalFibreMapTotalFibreNsmulSnd.lean#L39-L41

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

theorem ReciprocityTheory.PGsh.BX.Tmap_comp {R S T : LAlg R₀} (f : LHom R S) (g : LHom S T) (t : B.Tot R) :
    B.Tmap (g.comp f) t = B.Tmap g (B.Tmap f t) := by sorry
