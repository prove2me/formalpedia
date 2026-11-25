-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_T2_j__span_iso_41301ae96fc7
-- name    : P2M_ReciprocityTheory_ChartRestriction_T2_j__span_iso_41301ae96fc7
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T13:44:52.178372+00:00
-- url     : https://prove2.me/theorems/e235d304-2ef8-5f26-904f-77a966b7f5b3
-- title:
--   P2 M Reciprocity Theory Chart Restriction T2 j  span iso 41301ae96fc7: P2 M Reciprocity Theory Chart Restriction T2 j  span iso 41301ae96fc7
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction T2 j  span iso 41301ae96fc7 construction uses the P2 M Reciprocity Theory Chart Restriction T2 j  span iso 41301ae96fc7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/TraceFormulas/LatDefs.lean#L394-L403
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/TraceFormulas/LatDefs.lean#L394-L403

import Mathlib
import Definitions.Def_Formalism_WachLatticeTwists_LatticeDualFibres_FibreDualStable
import Definitions.Def_Formalism_WachLatticeTwists_CharacterSplitJumps_Statement
import Definitions.Def_Formalism_WachLatticeTwists_CoprimeLiftBounds_Statement
import Definitions.Def_Formalism_GaloisCohomology_LocalTateDualityK
import Definitions.Def_ReciprocityTheory_Hypotheses_GalCohDefs
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_TraceFormulas_LatDefs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.T2
open Formalism.NG Formalism.RepresentationBoundsCohomology.LOC Formalism.RepresentationBoundsCohomology.JT Formalism.RepresentationBoundsCohomology.BR
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
variable [hT2Core : Fact Core]

theorem P2M_ReciprocityTheory_ChartRestriction_T2_j__span_iso_41301ae96fc7 {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
    {VT VT' : Type}
    [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT]
    [ContinuousSMul O VT] [Module (FractionRing O) VT] [IsScalarTower O (FractionRing O) VT]
    [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT']
    [ContinuousSMul O VT'] [Module (FractionRing O) VT'] [IsScalarTower O (FractionRing O) VT'] {G : Type} [Group G] [TopologicalSpace G]
    (hO : PadicCoeff p O) (hF : FracTop O) (i : G ≃ₜ* GK p K) {D : LatData O G VT VT'} (hD : RealLatG i D) (y : H1 D.ρT') :
    ∃ c : O, c ≠ 0 ∧ c • y ∈ LinearMap.range D.j' := by sorry

alias «ReciprocityTheory».«ChartRestriction».«T2».«j'_span_iso» := P2M_ReciprocityTheory_ChartRestriction_T2_j__span_iso_41301ae96fc7
