-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_IrreducibleComponentPreimages_exists_open_compsH
-- name    : ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages.exists_open_compsH
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:52:11.049991+00:00
-- url     : https://prove2.me/theorems/724b4686-6955-4dd3-a2d8-7f78ef74e58f
-- title:
--   Irreducible Component Preimages: exists open comps H
-- statement:
--   The Irreducible Component Preimages construction uses the exists open comps H property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ClosureFromSpecMemCompsH.lean#L202-L262
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ClosureFromSpecMemCompsH.lean#L202-L262

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

theorem ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages.exists_open_compsH [IsNoetherian W] {Z : W.IdealSheafData} (y : W) (U : W.affineOpens)
    (hy : y ∈ U.1) {n : ℕ} (f : Fin n → Γ(W, U.1)) (J : Finset (Fin n))
    [IsRegularLocalRing (W.presheaf.stalk y)]
    (hrsp : FinalTheorems.Rsp (W.presheaf.stalk y) n (fun i => W.presheaf.germ U.1 y hy (f i)))
    (hZU : Z.ideal U = Ideal.span {∏ i ∈ J, f i}) :
    ∃ O : W.Opens, y ∈ O ∧ O ≤ U.1 ∧ ∀ C ∈ compsH (Z.support : Set W),
      C ∩ O = {z ∈ (O : Set W) | ∃ i ∈ J, IsBranchH (Z.support : Set W) (f i) y C ∧
        z ∈ W.zeroLocus {f i}} := by sorry
