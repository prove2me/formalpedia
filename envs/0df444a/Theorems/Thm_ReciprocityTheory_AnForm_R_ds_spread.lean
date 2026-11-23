-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_ds_spread
-- name    : ReciprocityTheory.AnForm.R.ds_spread
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:09:06.566886+00:00
-- url     : https://prove2.me/theorems/e15ff0e4-3efe-40c4-ac9f-101853592450
-- title:
--   R: ds spread
-- statement:
--   The R construction uses the ds spread property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/DivSheafA.lean#L45-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/DivSheafA.lean#L45-L149

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_FinalTheorems
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_DivSheafA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open AlgebraicGeometry CategoryTheory
noncomputable section
universe u

theorem ReciprocityTheory.AnForm.R.ds_spread {R S : Type*} [CommRing R] [IsNoetherianRing R] [CommRing S] [Algebra R S]
    (P : Ideal R) [P.IsPrime] [IsLocalization.AtPrime S P] (I : Ideal R) (a : R) (ha : a ∈ I)
    (hmap : I.map (algebraMap R S) = Ideal.span {algebraMap R S a})
    (hnzd : algebraMap R S a ∈ nonZeroDivisors S) :
    ∃ σ : R, σ ∉ P ∧ ∀ (T : Type*) [CommRing T] [Algebra R T] [IsLocalization.Away σ T],
      I.map (algebraMap R T) = Ideal.span {algebraMap R T a} ∧
        algebraMap R T a ∈ nonZeroDivisors T := by sorry
