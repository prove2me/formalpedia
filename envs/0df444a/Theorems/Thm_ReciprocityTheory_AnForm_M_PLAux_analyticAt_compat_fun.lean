-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_PLAux_analyticAt_compat_fun
-- name    : ReciprocityTheory.AnForm.M.PLAux.analyticAt_compat_fun
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T13:02:07.686972+00:00
-- url     : https://prove2.me/theorems/3bbfe751-0883-5986-bcbe-3c51b9645871
-- title:
--   PLAux: analytic At compat fun
-- statement:
--   The PLAux construction uses the analytic At compat fun property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/ContDiffMulOfTsupport.lean#L63-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/ContDiffMulOfTsupport.lean#L63-L72

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffHypInclAt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffMulOfTsupport
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.M.PLAux
open MeasureTheory FinHolAtlas Filter Topology
open ReciprocityTheory.AnForm.A (hypInclAt densHypAt)
open scoped ContDiff Manifold
noncomputable section
variable {e : ℕ} {X : Type} [TopologicalSpace X] [T2Space X] [CompactSpace X]
omit [T2Space X] [CompactSpace X]

theorem ReciprocityTheory.AnForm.M.PLAux.analyticAt_compat_fun {A : FinHolAtlas e X} {ψ : OpenPartialHomeomorph X (Fin e → ℂ)}
    (hψ : IsCompatChart A ψ) {U : Set X} {g : X → ℂ} (hg : A.HoloOn U g) {y : Fin e → ℂ}
    (hy : y ∈ ψ.target) (hyU : ψ.symm y ∈ U) : AnalyticAt ℂ (g ∘ ψ.symm) y := by sorry
