-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_BX_fibre_comm
-- name    : ReciprocityTheory.PGsh.BX.fibre_comm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:16:27.566717+00:00
-- url     : https://prove2.me/theorems/c4e77f74-5b90-4c95-9410-a12aaf46cc84
-- title:
--   BX: fibre comm
-- statement:
--   The BX construction uses the fibre comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/TotalFibreMapTotalFibreNsmulSnd.lean#L97-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/TotalFibreMapTotalFibreNsmulSnd.lean#L97-L99

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

theorem ReciprocityTheory.PGsh.BX.fibre_comm (hs : IsFibreSq p₁ p₂ f₁ f₂) : f₁.comp p₁ = f₂.comp p₂ := by sorry
