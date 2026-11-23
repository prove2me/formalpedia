-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_BX_pmap_congr_hom
-- name    : ReciprocityTheory.PGsh.BX.pmap_congr_hom
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:16:02.231516+00:00
-- url     : https://prove2.me/theorems/f071ac5b-c1e2-45e3-9273-59db9704fcb8
-- title:
--   BX: pmap congr hom
-- statement:
--   The BX construction uses the pmap congr hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/NsmulTensorEqZero.lean#L18-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/NsmulTensorEqZero.lean#L18-L21

import Definitions.Def_ReciprocityTheory_DualLattices_InstAddCommMonoidFibreFst
import Definitions.Def_ReciprocityTheory_DualLattices_NilSurjOfSqZero
import Definitions.Def_ReciprocityTheory_DualLattices_NsmulTensorEqZero
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
variable (B : BX R₀) {R : LAlg R₀} (Dp : DualPair R)

theorem ReciprocityTheory.PGsh.BX.pmap_congr_hom {S : LAlg R₀} {f g : LHom R S} (h : f = g) {x y : B.G R} (u : B.P R x y) :
    HEq (B.pmap f u) (B.pmap g u) := by sorry
