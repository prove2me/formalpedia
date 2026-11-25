-- Prove2me | Theorems.Thm_PI_WwInjectiveWork_gram_vanish
-- name    : PI.WwInjectiveWork.gram_vanish
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T08:46:03.631681+00:00
-- url     : https://prove2.me/theorems/9a81be88-5573-565e-886b-2e22d3938152
-- title:
--   Ww Injective Work: gram vanish
-- statement:
--   The Ww Injective Work construction uses the gram vanish property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GramInjectivity/GramVanish.lean#L9-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GramInjectivity/GramVanish.lean#L9-L48

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GramInjectivity_GramVanish
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WwInjectiveWork
open MvPolynomial

theorem PI.WwInjectiveWork.gram_vanish {σ ι K : Type*} [Fintype ι] [Field K] [CharZero K]
    (f : ι → MvPolynomial σ ℤ) (ph : MvPolynomial σ K →ₗ[K] K)
    (h : ∑ i, ph (map (Int.castRingHom K) (f i)) • map (Int.castRingHom K) (f i) = 0)
    (i : ι) : ph (map (Int.castRingHom K) (f i)) = 0 := by sorry
