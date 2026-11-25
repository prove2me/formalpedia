-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_IrreducibleComponentPreimages_existsUnique_branchH
-- name    : ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages.existsUnique_branchH
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T06:04:55.565644+00:00
-- url     : https://prove2.me/theorems/52b44527-6ab7-41b4-a59d-d0b729096ae3
-- title:
--   Irreducible Component Preimages: exists Unique branch H
-- statement:
--   The Irreducible Component Preimages construction uses the exists Unique branch H property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ClosureFromSpecMemCompsH.lean#L176-L184
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ClosureFromSpecMemCompsH.lean#L176-L184

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_PreMemIrreducibleComponents
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ClosureFromSpecMemCompsH
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages
open AlgebraicGeometry CategoryTheory TopologicalSpace
variable {W : Scheme.{0}}

theorem ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages.existsUnique_branchH [IsNoetherian W] {Z : W.IdealSheafData} (y : W) (U : W.affineOpens)
    (hy : y ∈ U.1) {n : ℕ} (f : Fin n → Γ(W, U.1)) (J : Finset (Fin n))
    [IsRegularLocalRing (W.presheaf.stalk y)]
    (hrsp : FinalTheorems.Rsp (W.presheaf.stalk y) n (fun i => W.presheaf.germ U.1 y hy (f i)))
    (hZU : Z.ideal U = Ideal.span {∏ i ∈ J, f i}) (i : Fin n) (hi : i ∈ J) :
    ∃! C, IsBranchH (Z.support : Set W) (f i) y C := by sorry
