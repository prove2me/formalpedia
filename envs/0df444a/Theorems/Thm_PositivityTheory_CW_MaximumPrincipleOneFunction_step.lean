-- Prove2me | Theorems.Thm_PositivityTheory_CW_MaximumPrincipleOneFunction_step
-- name    : PositivityTheory.CW.MaximumPrincipleOneFunction.step
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:50:40.540622+00:00
-- url     : https://prove2.me/theorems/87151127-658f-539a-afc9-83f3d92b53df
-- title:
--   Maximum Principle One Function: step
-- statement:
--   The Maximum Principle One Function construction uses the step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/MaximumPrincipleOfFacts.lean#L13-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/MaximumPrincipleOfFacts.lean#L13-L43

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_MaximumPrincipleOfFacts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset ReciprocityTheory.ChartRestriction.DS
open PositivityTheory PositivityTheory.CW
open PositivityTheory.CW.MaximumPrincipleOneFunction
variable {n : ℕ}

theorem PositivityTheory.CW.MaximumPrincipleOneFunction.step (hB3 : B3) (hB3g : UnitaryGroupFacts) (ε : Fin n → Bool) (r : ℕ) (u : Matrix (Fin n) (Fin n) ℂ → ℝ) (A η : ℝ)
    (g0 : Matrix (Fin n) (Fin n) ℂ)
    (hmax : ∀ g ∈ UJset ε, u g - A * (1 + hs2 g) ^ r - η * (1 + hs2 g) ^ (r + 1) ≤
      u g0 - A * (1 + hs2 g0) ^ r - η * (1 + hs2 g0) ^ (r + 1))
    (hg0 : g0 ∈ UJset ε) (p : Fin n × Fin n) (hp : p ∈ nc ε)
    (u' : ℝ → ℝ) (d : ℝ)
    (hu' : ∀ t, HasDerivAt (fun t : ℝ => u (g0 * NormedSpace.exp (t • Xp p.1 p.2))) (u' t) t)
    (hd : HasDerivAt u' d 0)
    (v' : ℝ → ℝ) (v'' : ℝ)
    (hv' : ∀ t, HasDerivAt (fun t : ℝ => (1 + hs2 (g0 * NormedSpace.exp (t • Xp p.1 p.2))) ^ r) (v' t) t)
    (hv'' : HasDerivAt v' v'' 0)
    (w' : ℝ → ℝ) (w'' : ℝ)
    (hw' : ∀ t, HasDerivAt (fun t : ℝ => (1 + hs2 (g0 * NormedSpace.exp (t • Xp p.1 p.2))) ^ (r + 1)) (w' t) t)
    (hw'' : HasDerivAt w' w'' 0) :
    d - A * v'' - η * w'' ≤ 0 := by sorry
