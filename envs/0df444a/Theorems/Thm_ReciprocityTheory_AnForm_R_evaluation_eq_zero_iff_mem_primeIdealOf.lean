-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_evaluation_eq_zero_iff_mem_primeIdealOf
-- name    : ReciprocityTheory.AnForm.R.evaluation_eq_zero_iff_mem_primeIdealOf
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T13:29:13.525534+00:00
-- url     : https://prove2.me/theorems/4f87381d-9316-546b-97a0-fc87768b0672
-- title:
--   R: evaluation eq zero iff mem prime Ideal Of
-- statement:
--   The R construction uses the evaluation eq zero iff mem prime Ideal Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ProjHypC.lean#L232-L240
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ProjHypC.lean#L232-L240

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjHypA
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjHypC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open MvPolynomial AlgebraicGeometry CategoryTheory
noncomputable section
variable {K : Type} [Fintype K] [Nonempty K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem ReciprocityTheory.AnForm.R.evaluation_eq_zero_iff_mem_primeIdealOf {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U)
    (x : X) (hx : x ∈ U) (s : Γ(X, U)) :
    X.evaluation U x hx s = 0 ↔ s ∈ (hU.primeIdealOf ⟨x, hx⟩).asIdeal := by sorry
