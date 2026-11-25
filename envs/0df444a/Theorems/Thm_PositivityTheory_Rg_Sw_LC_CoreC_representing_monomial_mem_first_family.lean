-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_representing_monomial_mem_first_family
-- name    : PositivityTheory.Rg.Sw.LC.CoreC.representing_monomial_mem_first_family
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:58:14.134683+00:00
-- url     : https://prove2.me/theorems/d4d4c932-85e8-50c1-8d8d-2eb640c22c65
-- title:
--   Core C: representing monomial mem first family
-- statement:
--   The Core C construction uses the representing monomial mem first family property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/FunctionalRepresentationByContraction.lean#L78-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/FunctionalRepresentationByContraction.lean#L78-L82

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_XPderivMono
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_FunctionalRepresentationByContraction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finsupp
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
open PositivityTheory.Rg.Sw.LC.CoreC
open PositivityTheory.Rg.Sw G
variable {m n : ℕ}

theorem PositivityTheory.Rg.Sw.LC.CoreC.representing_monomial_mem_first_family (ε : Fin m → Bool) (c : ℝ) (Λ : PX m n →ₗ[ℂ] ℂ) (s) : Bm ε c Λ s ∈ F1 ε := by sorry
