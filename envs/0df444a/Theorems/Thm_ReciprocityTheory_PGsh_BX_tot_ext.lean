-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_BX_tot_ext
-- name    : ReciprocityTheory.PGsh.BX.tot_ext
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:28:19.678813+00:00
-- url     : https://prove2.me/theorems/43eb9c67-e833-43f1-9538-478f7d5fe78c
-- title:
--   BX: tot ext
-- statement:
--   The BX construction uses the tot ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/TotalFibreMapTotalFibreNsmulSnd.lean#L24-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/TotalFibreMapTotalFibreNsmulSnd.lean#L24-L32

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

theorem ReciprocityTheory.PGsh.BX.tot_ext {R : LAlg R₀} {t t' : B.Tot R} (h1 : t.1 = t'.1) (h2 : t.2.1 = t'.2.1)
    (h3 : HEq t.2.2 t'.2.2) : t = t' := by sorry
