-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_IntPf_prod_pow_natDegree_coeff__4e974f93833c
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_IntPf_prod_pow_natDegree_coeff__4e974f93833c
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:13:41.7198+00:00
-- url     : https://prove2.me/theorems/5e18474a-1348-4fff-8124-7c1ca98bdc7a
-- title:
--   P2 M Reciprocity Theory Chart Restriction G AR Up Int Pf prod pow nat Degree coeff  4e974f93833c: P2 M Reciprocity Theory Chart Restriction G AR Up Int Pf prod pow nat Degree coeff  4e974f93833c
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G AR Up Int Pf prod pow nat Degree coeff  4e974f93833c construction uses the P2 M Reciprocity Theory Chart Restriction G AR Up Int Pf prod pow nat Degree coeff  4e974f93833c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/IntegralStatementPfA.lean#L95-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/IntegralStatementPfA.lean#L95-L99

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CapelliComplements_FirstLemmaA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_IntegralStatementPfA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.IntPf
noncomputable section
open Polynomial

theorem P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_IntPf_prod_pow_natDegree_coeff__4e974f93833c {B : Type*} [CommRing B] {ι : Type*} (s : Finset ι)
    (v : ι → B[X]) (d : ι → ℕ) (hv : ∀ i, (v i).natDegree ≤ 1) :
    (∏ i ∈ s, v i ^ d i).natDegree ≤ ∑ i ∈ s, d i ∧
      (∏ i ∈ s, v i ^ d i).coeff (∑ i ∈ s, d i) = ∏ i ∈ s, (v i).coeff 1 ^ d i := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«AR».«Up».«IntPf».«prod_pow_natDegree_coeff'» := P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_IntPf_prod_pow_natDegree_coeff__4e974f93833c
