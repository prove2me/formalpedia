-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_CasG_lhol_clm_eventually
-- name    : ReciprocityTheory.ChartRestriction.DS.S7.CasG.lhol_clm_eventually
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T14:08:20.690371+00:00
-- url     : https://prove2.me/theorems/e8af9711-9843-562d-8139-1c6d8ed2620c
-- title:
--   Cas G: lhol clm eventually
-- statement:
--   The Cas G construction uses the lhol clm eventually property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/LholClmEventually.lean#L46-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/LholClmEventually.lean#L46-L51

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PsiMLocal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CasLPsM
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CasChain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_LholClmEventually
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
open ReciprocityTheory.ChartRestriction.DS.S7.CasG
variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']

theorem ReciprocityTheory.ChartRestriction.DS.S7.CasG.lhol_clm_eventually (L : E →L[ℂ] E') (X : Matrix (Fin n) (Fin n) ℂ)
    {G : Matrix (Fin n) (Fin n) ℂ → E} {V : Set (Matrix (Fin n) (Fin n) ℂ)} (hV : IsOpen V)
    (hG : DifferentiableOn ℂ G V) {z : Matrix (Fin n) (Fin n) ℂ} (hz : z ∈ V) :
    Lhol X (fun w => L (G w)) =ᶠ[nhds z] fun w => L (Lhol X G w) := by sorry
