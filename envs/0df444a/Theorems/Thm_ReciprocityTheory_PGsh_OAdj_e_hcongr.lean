-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_OAdj_e_hcongr
-- name    : ReciprocityTheory.PGsh.OAdj.e_hcongr
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:33:21.020233+00:00
-- url     : https://prove2.me/theorems/198f7867-1ca5-4a8c-a14c-90ae88d843d7
-- title:
--   OAdj: e hcongr
-- statement:
--   The OAdj construction uses the e hcongr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/SubMemSpan.lean#L18-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/SubMemSpan.lean#L18-L21

import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_IsPairingValueAddRight
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemSpan
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
open ReciprocityTheory.PGsh.OAdj
variable {B : BX R₀} {O : LAlg R₀} (A : OAdj B O) {R : LAlg R₀} (s : LHom O R)

theorem ReciprocityTheory.PGsh.OAdj.e_hcongr {x₁ x₂ z₁ z₂ : B.G R} (hx : x₁ = x₂) (hz : z₁ = z₂)
    {u₁ : B.P R (A.a.f s x₁) z₁} {u₂ : B.P R (A.a.f s x₂) z₂} (hu : HEq u₁ u₂) :
    HEq (A.e s x₁ z₁ u₁) (A.e s x₂ z₂ u₂) := by sorry
