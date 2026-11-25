-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_BX_ext_of_isFibreSq
-- name    : ReciprocityTheory.PGsh.BX.ext_of_isFibreSq
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T11:06:06.890195+00:00
-- url     : https://prove2.me/theorems/56469255-48c3-4ed4-a00d-a59c3630071c
-- title:
--   BX: ext of is Fibre Sq
-- statement:
--   The BX construction uses the ext of is Fibre Sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/TotalFibreMapTotalFibreNsmulSnd.lean#L112-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/TotalFibreMapTotalFibreNsmulSnd.lean#L112-L116

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

theorem ReciprocityTheory.PGsh.BX.ext_of_isFibreSq (hs : IsFibreSq p₁ p₂ f₁ f₂) {c c' : B.Tot F}
    (h1 : B.Tmap p₁ c = B.Tmap p₁ c') (h2 : B.Tmap p₂ c = B.Tmap p₂ c') : c = c' := by sorry
