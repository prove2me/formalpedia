-- Prove2me | Theorems.Thm_PI_GalTorsConj_W_core
-- name    : PI.GalTorsConj.W.core
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T13:46:25.708985+00:00
-- url     : https://prove2.me/theorems/342510e0-1148-56d6-ba78-81e23812c491
-- title:
--   W: core
-- statement:
--   The W construction uses the core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GaloisTorsionConjugacy/MulCore.lean#L34-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GaloisTorsionConjugacy/MulCore.lean#L34-L153

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_MulMain
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeierstrassUniformization_PairIsLat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_MulCore
import Theorems.Thm_Formalism_L2_Th1_F_EtaEis_core
import Theorems.Thm_Formalism_L2_Th1_F_ThreeTermRelation_core

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

theorem PI.GalTorsConj.W.core (hD : IsogD) (hO : IsogODE) (hDn : TorsDense)
    (hg2 : L.g₂ ∈ M₁) (hg3 : L.g₃ ∈ M₁) (hg2' : L'.g₂ = ρ₁ ⟨_, hg2⟩) (hg3' : L'.g₃ = ρ₁ ⟨_, hg3⟩)
    (htors : ∀ (n : ℕ) (t : ℂ), 0 < n → (n : ℂ) * t ∈ L.lattice → t ∉ L.lattice →
      L.weierstrassP t ∈ M₁ ∧ L.derivWeierstrassP t ∈ M₁)
    {c : ℂ} (hc0 : c ≠ 0) (hcL : MulStable L c) (hc : c ∈ M₁) (hρc : ρ₁ ⟨c, hc⟩ = c)
    {t t' : ℂ} (h : St L L' M₁ ρ₁ t t') : St L L' M₁ ρ₁ (c * t) (c * t') := by sorry
