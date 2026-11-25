-- Prove2me | Theorems.Thm_PI_QnCovHat2W_reindex_pairs
-- name    : PI.QnCovHat2W.reindex_pairs
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T06:00:34.47346+00:00
-- url     : https://prove2.me/theorems/5e1665e3-9a7a-4ff5-8b6e-4c0c071f4732
-- title:
--   Qn Cov Hat2 W: reindex pairs
-- statement:
--   The Qn Cov Hat2 W construction uses the reindex pairs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CovariantHatPairReindex/SkipTwoOfGe.lean#L140-L193
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CovariantHatPairReindex/SkipTwoOfGe.lean#L140-L193

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CovariantHatPairReindex_SkipTwoOfGe
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

theorem PI.QnCovHat2W.reindex_pairs {m : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M]
    (F : (Fin m → Fin (m + 2)) → M) (β β' : Fin (m + 2) → ℂ) :
    ∑ j : Fin (m + 2), ∑ j' : Fin (m + 1),
        ((-1 : ℂ) ^ ((j : ℕ) + (j' : ℕ)) * (β j * β' (j.succAbove j'))) •
          F (fun k => j.succAbove (j'.succAbove k)) =
      ∑ i : Fin (m + 2), ∑ i' : Fin (m + 2),
        if i < i' then ((-1 : ℂ) ^ ((i : ℕ) + (i' : ℕ)) * (β i' * β' i - β i * β' i')) •
          F (skip2 i i') else 0 := by sorry
