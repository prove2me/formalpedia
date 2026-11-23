-- Prove2me | Theorems.Thm_PI_WickFormula_Gen_mem_lowDeg
-- name    : PI.WickFormula.Gen.mem_lowDeg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:37:48.560253+00:00
-- url     : https://prove2.me/theorems/a75b81ca-248b-4259-bcf8-7e6f74bfb2ff
-- title:
--   Gen: mem low Deg
-- statement:
--   The Gen construction uses the mem low Deg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/DiscriminantEstimates/DiscriminantLemmas/WickFormula/GenVan.lean#L13-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/DiscriminantEstimates/DiscriminantLemmas/WickFormula/GenVan.lean#L13-L17

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

theorem PI.WickFormula.Gen.mem_lowDeg {f : ι → σ} {t : ℕ} {R : MvPolynomial σ K} :
    R ∈ lowDeg f t ↔ ∀ m ∈ R.support, ∑ i, m (f i) < t := by sorry
