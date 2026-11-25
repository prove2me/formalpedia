-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_prod_map_ite_one
-- name    : ReciprocityTheory.PGsh.prod_map_ite_one
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:09:24.766913+00:00
-- url     : https://prove2.me/theorems/5f8cd705-6cb9-42f2-8fb6-a48866d03b74
-- title:
--   PGsh: prod map ite one
-- statement:
--   The PGsh construction uses the prod map ite one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/DetPolyMulCayleyOmegaPow.lean#L54-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/DetPolyMulCayleyOmegaPow.lean#L54-L59

import Definitions.Def_ReciprocityTheory_DualLattices_FischerAdjointStatement
import Definitions.Def_ReciprocityTheory_DualLattices_DetPolyMulCayleyOmegaPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Matrix Finset
open ReciprocityTheory ReciprocityTheory.PGsh
variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

theorem ReciprocityTheory.PGsh.prod_map_ite_one {M ι : Type*} [Monoid M] (l : List ι) (p : ι → Prop) [DecidablePred p]
    (d : ι → M) :
    (l.map fun j => if p j then d j else 1).prod = ((l.filter fun j => p j).map d).prod := by sorry
