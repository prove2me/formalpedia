-- Prove2me | Theorems.Thm_PI_GalTorsConj_W_conj_velu_isogeny
-- name    : PI.GalTorsConj.W.conj_velu_isogeny
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:58:30.162398+00:00
-- url     : https://prove2.me/theorems/ae611ec0-31c6-4f1c-80a6-421844fef8b9
-- title:
--   W: conj velu isogeny
-- statement:
--   The W construction uses the conj velu isogeny property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GaloisTorsionConjugacy/MulCore.lean#L15-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GaloisTorsionConjugacy/MulCore.lean#L15-L32

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_MulMain
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeierstrassUniformization_PairIsLat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_MulCore
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.GalTorsConj PI.GalTorsConj.W
open PI.GalTorsConj Formalism.L2.Th1.F
variable {L L' : PeriodPair} {M₁ : IntermediateField ℚ ℂ} {ρ₁ : M₁ →ₐ[ℚ] ℂ}

theorem PI.GalTorsConj.W.conj_velu_isogeny (hg2 : L.g₂ ∈ M₁) (hg2' : L'.g₂ = ρ₁ ⟨_, hg2⟩) {S : Finset ℂ} {f : ℂ → ℂ}
    (hf : ∀ P ∈ S, St L L' M₁ ρ₁ P (f P)) (hinj : Set.InjOn f S)
    (hSL : ∀ P ∈ S, P ∉ L.lattice) {z z' : ℂ} (hz : St L L' M₁ ρ₁ z z')
    (hU : z ∈ veluU L S) :
    Cj1 M₁ ρ₁ (veluF L S z) (veluF L' (S.image f) z') ∧
      Cj1 M₁ ρ₁ (veluD L S z) (veluD L' (S.image f) z') := by sorry
