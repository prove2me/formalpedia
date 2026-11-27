-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_Glob_VacS_ftG_DG
-- name    : PositivityTheory.Rg.Sw.Glob.VacS.ftG_DG
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T13:53:12.900845+00:00
-- url     : https://prove2.me/theorems/3ca29cf1-938d-4176-97fd-689f680c829b
-- title:
--   Vac S: ft G DG
-- statement:
--   The Vac S construction uses the ft G DG property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GlobalGaussLaws/GaussScalar.lean#L41-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GlobalGaussLaws/GaussScalar.lean#L41-L97

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GlobalGaussLaws_GaussScalar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex MeasureTheory
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.Glob PositivityTheory.Rg.Sw.Glob.VacS

theorem PositivityTheory.Rg.Sw.Glob.VacS.ftG_DG {m n : ℕ} (σ : Fin m → ℝ) (s : ℝ) (K : ℂ) (γ : Fin m → Fin n → ℂ) (hγ : ∀ a j, 0 < (γ a j).re)
    (u : Fin m → Fin n → ℂ) :
    ftG σ s (DG K γ) u = DG (K * ∏ a, ∏ j, ((Real.pi : ℂ) / γ a j))
      (fun a j => (s : ℂ) ^ 2 * ((σ a : ℂ) ^ 2) / γ a j) u := by sorry
