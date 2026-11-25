-- Prove2me | Theorems.Thm_PI_WickFormula_Gen_eq_zero_of_mem_lowDeg_zero
-- name    : PI.WickFormula.Gen.eq_zero_of_mem_lowDeg_zero
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:45:21.227621+00:00
-- url     : https://prove2.me/theorems/781d09d6-01ce-5ff8-a2e1-f802dcc69c20
-- title:
--   Gen: eq zero of mem low Deg zero
-- statement:
--   The Gen construction uses the eq zero of mem low Deg zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/DiscriminantEstimates/DiscriminantLemmas/WickFormula/GenVan.lean#L19-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/DiscriminantEstimates/DiscriminantLemmas/WickFormula/GenVan.lean#L19-L25

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

theorem PI.WickFormula.Gen.eq_zero_of_mem_lowDeg_zero {f : ι → σ} {R : MvPolynomial σ K}
    (h : R ∈ lowDeg f 0) : R = 0 := by sorry
