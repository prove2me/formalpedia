-- Prove2me | Theorems.Thm_P2M_GenFrameSpan_basisMonomials_apply__3e1a67869174
-- name    : P2M_GenFrameSpan_basisMonomials_apply__3e1a67869174
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:08:25.025697+00:00
-- url     : https://prove2.me/theorems/0a51132a-7aca-438f-a863-1f243f9539bf
-- title:
--   P2 M Gen Frame Span basis Monomials apply  3e1a67869174: P2 M Gen Frame Span basis Monomials apply  3e1a67869174
-- statement:
--   The P2 M Gen Frame Span basis Monomials apply  3e1a67869174 construction uses the P2 M Gen Frame Span basis Monomials apply  3e1a67869174 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MonomialFrameSpan/BasisMonomialsApply.lean#L32-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MonomialFrameSpan/BasisMonomialsApply.lean#L32-L34

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MonomialFrameSpan_NablaSpanC
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MonomialFrameSpan_DetSubmatrixFun
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MonomialFrameSpan_BasisMonomialsApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open GenFrameSpan
open CutKW MvPolynomial
variable {Lt : Type} [Fintype Lt] [DecidableEq Lt] {N0 N1 l : ℕ} [Fact l.Prime]

theorem P2M_GenFrameSpan_basisMonomials_apply__3e1a67869174 {σ : Type} (μ : σ →₀ ℕ) :
    basisMonomials σ ℤ μ = monomial μ (1 : ℤ) := by sorry

alias «GenFrameSpan».«basisMonomials_apply'» := P2M_GenFrameSpan_basisMonomials_apply__3e1a67869174
