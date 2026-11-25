-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_ApproximationGraph_approxGraph_three
-- name    : ReciprocityTheory.MultiplicativeHeights.ApproximationGraph.approxGraph_three
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T11:01:19.163114+00:00
-- url     : https://prove2.me/theorems/35b1059e-ad69-5004-bf99-e5c0e621c75d
-- title:
--   Approximation Graph: approx Graph three
-- statement:
--   The Approximation Graph construction uses the approx Graph three property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/ApproxGraphC.lean#L107-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/ApproxGraphC.lean#L107-L148

import Definitions.Def_ReciprocityTheory_SemistableReduction_ApproxGraphB
import Definitions.Def_ReciprocityTheory_SemistableReduction_ApproxGraphC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.ApproximationGraph
open ComplexConjugate

theorem ReciprocityTheory.MultiplicativeHeights.ApproximationGraph.approxGraph_three {r p : ℕ} {μ ρ : ℝ} (X : Fin r → Fin r → ℂ) (hμ : 0 < μ) (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1)
    (hX : ∀ j : Fin r, (j : ℕ) < p →
      normSq (X j - (approxR r μ ρ : ℂ) • (Pi.single j 1 : Fin r → ℂ)) ≤ μ ^ 2)
    (v y : Fin r → ℂ) (hy : ∀ j : Fin r, (j : ℕ) < p → jForm p (X j) y = 0)
    (hvy : v - y ∈ Submodule.span ℂ (X '' {j | (j : ℕ) < p})) :
    ‖jForm p y y‖ ≤ 2 * normSq v := by sorry
