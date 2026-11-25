-- Prove2me | Theorems.Thm_PositivityTheory_KReal_supp_wt_term
-- name    : PositivityTheory.KReal.supp_wt_term
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:40:08.926645+00:00
-- url     : https://prove2.me/theorems/ca7295cb-82e4-43c0-aa22-78683dae6cf8
-- title:
--   KReal: supp wt term
-- statement:
--   The KReal construction uses the supp wt term property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreSupp.lean#L32-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreSupp.lean#L32-L54

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

theorem PositivityTheory.KReal.supp_wt_term (w : σ → ℕ) (l l' : σ) (P : MvPolynomial σ ℂ) (γ : σ →₀ ℕ)
    (h : coeff γ (X l * pderiv l' P) ≠ 0) :
    ∃ β ∈ P.support, Finsupp.weight w β + w l = Finsupp.weight w γ + w l' := by sorry
