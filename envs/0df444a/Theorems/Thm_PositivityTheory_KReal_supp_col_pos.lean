-- Prove2me | Theorems.Thm_PositivityTheory_KReal_supp_col_pos
-- name    : PositivityTheory.KReal.supp_col_pos
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:39:17.829525+00:00
-- url     : https://prove2.me/theorems/07dd6542-155c-59c1-be3f-be83e8a51e77
-- title:
--   KReal: supp col pos
-- statement:
--   The KReal construction uses the supp col pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreSupp.lean#L299-L327
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreSupp.lean#L299-L327

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
variable {p q r s : ℕ} {ν : Ix r s → ℚ} {g : Pol p q r s}

theorem PositivityTheory.KReal.supp_col_pos (hg : IsHW (fockAct2 p q r s) ν g) {N : ℕ} (d : Ix r s) (ρ : Fin N → Ix p q)
    (hρ : ∀ a, linePos ((a, d) : Ln p q r s) = true ↔ ∃ i, ρ i = a) (hρi : Function.Injective ρ)
    (κ : Fin N → Ix r s) (hκ : Function.Injective κ) (hκd : ∀ j, posC (κ j) d) :
    shiftNu (cPair p q) ν d ≤ 0 := by sorry
