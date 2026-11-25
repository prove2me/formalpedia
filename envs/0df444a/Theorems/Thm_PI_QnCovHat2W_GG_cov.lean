-- Prove2me | Theorems.Thm_PI_QnCovHat2W_GG_cov
-- name    : PI.QnCovHat2W.GG_cov
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T06:00:27.025801+00:00
-- url     : https://prove2.me/theorems/88f08b01-f59f-4d69-aa16-2403aa4f018a
-- title:
--   Qn Cov Hat2 W: GG cov
-- statement:
--   The Qn Cov Hat2 W construction uses the GG cov property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CovariantHatPairReindex/SumSgnLProdCol.lean#L69-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CovariantHatPairReindex/SumSgnLProdCol.lean#L69-L144

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CovariantHatPairReindex_GGEq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CovariantHatPairReindex_SumSgnLProdCol
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

theorem PI.QnCovHat2W.GG_cov {m : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M]
    (F F' : (Fin m → Fin (m + 2)) → (Fin m → Fin (m + 2)) → M)
    (P Q : Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ)
    (hLin : ∀ x y : Fin m → Fin (m + 2), F' x y =
      ∑ c : Fin m → Fin (m + 2), ∑ d : Fin m → Fin (m + 2),
        ((∏ k, P (c k) (x k)) * ∏ k, Q (y k) (d k)) • F c d)
    (β β' a a' : Fin (m + 2) → ℂ) :
    GG F' (β ᵥ* P) (β' ᵥ* P) (Q *ᵥ a) (Q *ᵥ a') = (P.det * Q.det) • GG F β β' a a' := by sorry
