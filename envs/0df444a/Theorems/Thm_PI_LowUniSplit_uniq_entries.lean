-- Prove2me | Theorems.Thm_PI_LowUniSplit_uniq_entries
-- name    : PI.LowUniSplit.uniq_entries
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:35:08.719841+00:00
-- url     : https://prove2.me/theorems/00d1c778-d1f9-4c79-98f9-7fc82eebe169
-- title:
--   Low Uni Split: uniq entries
-- statement:
--   The Low Uni Split construction uses the uniq entries property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LowerUnipotentSplit/SecondFactorMemLowerTriangular.lean#L162-L193
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LowerUnipotentSplit/SecondFactorMemLowerTriangular.lean#L162-L193

import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LowerUnipotentSplit_SecondFactorMemLowerTriangular
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.LowUniSplit
open Formalism.FourierDecayAlt.C2
variable {m : ℕ}
variable (S : Fin m → Fin m → Prop) [DecidableRel S] (l : Matrix (Fin m) (Fin m) ℂ)

theorem PI.LowUniSplit.uniq_entries {a b : Matrix (Fin m) (Fin m) ℂ}
    (ha : a ∈ LTset m) (hb : b ∈ LTset m)
    (hsa : ∀ i j, j < i → ¬ S i j → a i j = 0) (hsb : ∀ i j, j < i → S i j → b i j = 0)
    (hab : l = a * b) :
    ∀ n : ℕ, ∀ i j : Fin m, (i : ℕ) - j = n → j < i →
      a i j = (if S i j then xs S l i j else 0) ∧ b i j = (if S i j then 0 else xs S l i j) := by sorry
