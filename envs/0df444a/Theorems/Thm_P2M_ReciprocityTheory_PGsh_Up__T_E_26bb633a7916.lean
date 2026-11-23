-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_PGsh_Up__T_E_26bb633a7916
-- name    : P2M_ReciprocityTheory_PGsh_Up__T_E_26bb633a7916
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:28:57.963737+00:00
-- url     : https://prove2.me/theorems/aeda3fa4-1997-40ed-8a1a-54cc5a17011e
-- title:
--   P2 M Reciprocity Theory PGsh Up  T E 26bb633a7916: P2 M Reciprocity Theory PGsh Up  T E 26bb633a7916
-- statement:
--   The P2 M Reciprocity Theory PGsh Up  T E 26bb633a7916 construction uses the P2 M Reciprocity Theory PGsh Up  T E 26bb633a7916 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/UnramifiedCokernelLengthOfLengthEigenLengthProduct.lean#L64-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/UnramifiedCokernelLengthOfLengthEigenLengthProduct.lean#L64-L84

import Definitions.Def_ReciprocityTheory_DualLattices_EigenLengthFrobeniusStatement
import Definitions.Def_ReciprocityTheory_DualLattices_FrobEqOfLe
import Definitions.Def_ReciprocityTheory_DualLattices_StdJForm
import Definitions.Def_ReciprocityTheory_DualLattices_UnramifiedCokernelLowerBoundOf
import Definitions.Def_ReciprocityTheory_DualLattices_UnramifiedCokernelLengthOfLengthEigenLengthProduct
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up
open ReciprocityTheory.PGsh.L2
variable {p : ℕ} [Fact p.Prime] {g : ℕ} {C : Type} [Field C] {v : Valuation C NNReal} {R : Type}
  [CommRing R] [Algebra R C] [Algebra ℤ_[p] R] {O : Type} [CommRing O] [Algebra ℤ_[p] O]
  {σ : O ≃ₐ[ℤ_[p]] O} {cp : R}

theorem P2M_ReciprocityTheory_PGsh_Up__T_E_26bb633a7916 (hS : HodgeTateSetting p v R O σ cp) (H : HodgeTateDatum p g v R O σ cp)
    (U : UnramData p g v R O σ cp H) (i : Fin U.m) :
    (U.εT i)ᵀ * H.E.map (algebraMap ℤ_[p] R) = H.E.map (algebraMap ℤ_[p] R) * U.εT (U.cj i) := by sorry

alias «ReciprocityTheory».«PGsh».«Up».«εT_E» := P2M_ReciprocityTheory_PGsh_Up__T_E_26bb633a7916
