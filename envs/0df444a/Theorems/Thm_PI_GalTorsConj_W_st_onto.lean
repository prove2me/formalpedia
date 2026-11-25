-- Prove2me | Theorems.Thm_PI_GalTorsConj_W_st_onto
-- name    : PI.GalTorsConj.W.st_onto
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:31:37.575323+00:00
-- url     : https://prove2.me/theorems/baee0db0-2e72-4c2b-84be-ff42265db6ab
-- title:
--   W: st onto
-- statement:
--   The W construction uses the st onto property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GaloisTorsionConjugacy/StAddRight.lean#L265-L319
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GaloisTorsionConjugacy/StAddRight.lean#L265-L319

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_WpBridge
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_StAddRight
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
open Formalism.L2.Th1.F
variable {L L' : PeriodPair} {M : IntermediateField ℚ ℂ} {ρ : M →ₐ[ℚ] ℂ}

theorem PI.GalTorsConj.W.st_onto (hA : AddLaw) (hD : DblLaw) (hO : POnto) (hg2 : L.g₂ ∈ M) (hg3 : L.g₃ ∈ M)
    (hg2' : L'.g₂ = ρ ⟨_, hg2⟩) (hg3' : L'.g₃ = ρ ⟨_, hg3⟩) (n : ℕ) (hn : 0 < n)
    (hM : ∀ t, (n : ℂ) * t ∈ L.lattice → t ∉ L.lattice →
      L.weierstrassP t ∈ M ∧ L.derivWeierstrassP t ∈ M)
    (t' : ℂ) (ht' : (n : ℂ) * t' ∈ L'.lattice) :
    ∃ t, (n : ℂ) * t ∈ L.lattice ∧ St L L' M ρ t t' := by sorry
