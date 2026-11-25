-- Prove2me | Theorems.Thm_PI_WickFormula_Gen_pderiv_mem_lowDeg_of_succ
-- name    : PI.WickFormula.Gen.pderiv_mem_lowDeg_of_succ
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:46:35.175491+00:00
-- url     : https://prove2.me/theorems/182e3711-c711-5cc3-8cce-929c87c470af
-- title:
--   Gen: pderiv mem low Deg of succ
-- statement:
--   The Gen construction uses the pderiv mem low Deg of succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/DiscriminantEstimates/DiscriminantLemmas/WickFormula/GenVan.lean#L43-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/DiscriminantEstimates/DiscriminantLemmas/WickFormula/GenVan.lean#L43-L64

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_WickFormula_GenDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_WickFormula_GenVan
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open PI PI.WickFormula PI.WickFormula.Gen
variable {K σ ι : Type} [CommRing K] [Fintype ι]

theorem PI.WickFormula.Gen.pderiv_mem_lowDeg_of_succ {f : ι → σ} {t : ℕ} (i : ι) {R : MvPolynomial σ K}
    (h : R ∈ lowDeg f (t + 1)) : pderiv (f i) R ∈ lowDeg f t := by sorry
