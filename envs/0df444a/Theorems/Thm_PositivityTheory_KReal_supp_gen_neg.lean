-- Prove2me | Theorems.Thm_PositivityTheory_KReal_supp_gen_neg
-- name    : PositivityTheory.KReal.supp_gen_neg
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:45:13.124208+00:00
-- url     : https://prove2.me/theorems/8baf9eb0-2a14-5a40-bc8c-d23eb92f47a4
-- title:
--   KReal: supp gen neg
-- statement:
--   The KReal construction uses the supp gen neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreSupp.lean#L252-L271
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreSupp.lean#L252-L271

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreLie
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreSupp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.ThetaSummability.Real ReciprocityTheory.ChartRestriction.G.ThK.Real FockH1Action MvPolynomial Matrix
open scoped InnerProductSpace
open PositivityTheory PositivityTheory.KReal
variable {σ κ : Type} [Fintype κ]

theorem PositivityTheory.KReal.supp_gen_neg {N : ℕ} (pos : κ → Bool) (ρ : Fin N → κ) (hρ : ∀ c, pos c = false ↔ ∃ i, ρ i = c)
    (hρi : Function.Injective ρ) (u : Fin N → κ → σ) (v : κ → σ)
    (hu : Function.Injective (fun x : Fin N × Fin N => u x.1 (ρ x.2)))
    (huv : ∀ j c c', u j c ≠ v c') (hv : Function.Injective v) (P : MvPolynomial σ ℂ) (hP : P ≠ 0)
    (hR : ∀ j, PI.FJMP.gR v (u j) pos P = 0) : ∃ e ∈ P.support, 0 ≤ PI.FJMP.sw e v pos := by sorry
