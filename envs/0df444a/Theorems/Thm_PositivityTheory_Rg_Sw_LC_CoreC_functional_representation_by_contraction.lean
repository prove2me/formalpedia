-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_functional_representation_by_contraction
-- name    : PositivityTheory.Rg.Sw.LC.CoreC.functional_representation_by_contraction
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:57:21.358205+00:00
-- url     : https://prove2.me/theorems/5648d526-440a-463c-802d-9ff8689dda90
-- title:
--   Core C: functional representation by contraction
-- statement:
--   The Core C construction uses the functional representation by contraction property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/FunctionalRepresentationByContraction.lean#L123-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/FunctionalRepresentationByContraction.lean#L123-L131

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

theorem PositivityTheory.Rg.Sw.LC.CoreC.functional_representation_by_contraction (ε : Fin m → Bool) {c : ℝ} (hc : 0 < c) (Λ : PX m n →ₗ[ℂ] ℂ) (hΛ : ∀ a b p, Λ (Dop ε c a b p) = 0)
    {f g : PX m n} (hf : f ∈ F1 ε) (hg : g ∈ F2 ε) : Λ (f * g) = contr c (Bop ε c Λ f * g) := by sorry
