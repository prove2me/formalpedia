-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_BX_exists_lift_of_isFibreSq
-- name    : ReciprocityTheory.PGsh.BX.exists_lift_of_isFibreSq
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:05:27.866257+00:00
-- url     : https://prove2.me/theorems/9539ad24-6493-5573-b67d-e3a47ee0be1d
-- title:
--   BX: exists lift of is Fibre Sq
-- statement:
--   The BX construction uses the exists lift of is Fibre Sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/TotalFibreMapTotalFibreNsmulSnd.lean#L107-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/TotalFibreMapTotalFibreNsmulSnd.lean#L107-L110

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
variable {F R₁ R₂ R : LAlg R₀} {p₁ : LHom F R₁} {p₂ : LHom F R₂} {f₁ : LHom R₁ R}
  {f₂ : LHom R₂ R}

theorem ReciprocityTheory.PGsh.BX.exists_lift_of_isFibreSq (hs : IsFibreSq p₁ p₂ f₁ f₂) (a : B.Tot R₁) (b : B.Tot R₂)
    (h : B.Tmap f₁ a = B.Tmap f₂ b) : ∃ c : B.Tot F, B.Tmap p₁ c = a ∧ B.Tmap p₂ c = b := by sorry
