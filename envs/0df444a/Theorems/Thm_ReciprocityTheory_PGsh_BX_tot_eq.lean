-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_BX_tot_eq
-- name    : ReciprocityTheory.PGsh.BX.tot_eq
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T11:05:52.596721+00:00
-- url     : https://prove2.me/theorems/7e8d49d7-17ec-52a1-9a17-807d2a6908f8
-- title:
--   BX: tot eq
-- statement:
--   The BX construction uses the tot eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/TotalFibreMapTotalFibreNsmulSnd.lean#L34-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/TotalFibreMapTotalFibreNsmulSnd.lean#L34-L37

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

theorem ReciprocityTheory.PGsh.BX.tot_eq {R : LAlg R₀} {t t' : B.Tot R} (h : t = t') :
    t.1 = t'.1 ∧ t.2.1 = t'.2.1 ∧ HEq t.2.2 t'.2.2 := by sorry
