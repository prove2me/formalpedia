-- Prove2me | Theorems.Thm_PI_VolStabW_FiniteFieldSplitting_fFSplit_nat
-- name    : PI.VolStabW.FiniteFieldSplitting.fFSplit_nat
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T08:37:17.059032+00:00
-- url     : https://prove2.me/theorems/0561f413-b92d-4d1a-a15c-925d71ec1311
-- title:
--   Finite Field Splitting: f FSplit nat
-- statement:
--   The Finite Field Splitting construction uses the f FSplit nat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/LocDensFFS.lean#L166-L209
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/LocDensFFS.lean#L166-L209

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensFF
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensFFS
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open PI.VolStabW.FiniteFieldSplitting
open Matrix
variable {k : Type} [Field k] [Finite k] {M a : ℕ}

theorem PI.VolStabW.FiniteFieldSplitting.fFSplit_nat (M a : ℕ) (ha : a ≤ M)
    (J : Matrix (Fin M) (Fin M) (k × k)) (hJ : ∀ i j, (J j i).swap = J i j) (hJd : IsUnit J.det)
    (T : Matrix (Fin a) (Fin a) (k × k)) (hT : ∀ i j, (T j i).swap = T i j) (hTd : IsUnit T.det) :
    Nat.card {X : Fin a → Fin M → k × k // ffGram (swapR k) J X = T} =
      (∏ i : Fin a, (Nat.card k ^ M - Nat.card k ^ (i : ℕ))) * Nat.card k ^ (a * (M - a)) := by sorry
