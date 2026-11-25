-- Prove2me | Theorems.Thm_PI_QnCovHat2W_one_side
-- name    : PI.QnCovHat2W.one_side
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:41:32.124806+00:00
-- url     : https://prove2.me/theorems/4dcc406d-3723-427e-9813-71dd1bf53708
-- title:
--   Qn Cov Hat2 W: one side
-- statement:
--   The Qn Cov Hat2 W construction uses the one side property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CovariantHatPairReindex/GGEq.lean#L9-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CovariantHatPairReindex/GGEq.lean#L9-L24

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CovariantHatPairReindex_SkipTwoOfGe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CovariantHatPairReindex_GGEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open PI PI.QnCovHat2W
open Formalism.REAL Formalism.FourierDecayAlt.Q

theorem PI.QnCovHat2W.one_side {m : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M]
    (F : (Fin m → Fin (m + 2)) → M)
    (hF : ∀ (x : Fin m → Fin (m + 2)) (π : Equiv.Perm (Fin m)),
      F (x ∘ π) = ((Equiv.Perm.sign π : ℤ) : ℂ) • F x)
    (β β' : Fin (m + 2) → ℂ) :
    ∑ c : Fin (m + 2) → Fin (m + 2), sgnL c id • ((β (c 0) * β' (c 1)) • F (fun k => c k.succ.succ)) =
      (m.factorial : ℂ) • ∑ i : Fin (m + 2), ∑ i' : Fin (m + 2),
        if i < i' then ((-1 : ℂ) ^ ((i : ℕ) + (i' : ℕ)) * (β i' * β' i - β i * β' i')) •
          F (skip2 i i') else 0 := by sorry
