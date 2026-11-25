-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_BX_fibreG_unique
-- name    : ReciprocityTheory.PGsh.BX.fibreG_unique
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T11:05:37.855828+00:00
-- url     : https://prove2.me/theorems/603128d4-0d03-5a92-be09-31f29a522d18
-- title:
--   BX: fibre G unique
-- statement:
--   The BX construction uses the fibre G unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/TotalFibreMapTotalFibreNsmulSnd.lean#L101-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/TotalFibreMapTotalFibreNsmulSnd.lean#L101-L105

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

theorem ReciprocityTheory.PGsh.BX.fibreG_unique (hs : IsFibreSq p₁ p₂ f₁ f₂) {a b : B.G F} (h1 : B.map p₁ a = B.map p₁ b)
    (h2 : B.map p₂ a = B.map p₂ b) : a = b := by sorry
