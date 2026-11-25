-- Prove2me | Theorems.Thm_PI_LocCartanPair_lag_congr
-- name    : PI.LocCartanPair.lag_congr
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:35:22.247817+00:00
-- url     : https://prove2.me/theorems/214061a2-5dc3-42a2-aa27-abbdb492ed4b
-- title:
--   Loc Cartan Pair: lag congr
-- statement:
--   The Loc Cartan Pair construction uses the lag congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalCartanPairs/PairBaseOfLag.lean#L14-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalCartanPairs/PairBaseOfLag.lean#L14-L40

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_UnimodUnramUnique
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_PairBaseOfLag
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LocCartanPair
open Matrix IsLocalRing
variable {R : Type} [CommRing R] [StarRing R]

theorem PI.LocCartanPair.lag_congr {ι : Type} [Fintype ι] [DecidableEq ι] (A B P e : Matrix ι ι R)
    (hP : IsUnit P.det) (hPAB : Pᴴ * A * P = B) (he : e * e = e)
    (heB : eᴴ * B = B * (1 - e)) :
    (P * e * P⁻¹) * (P * e * P⁻¹) = P * e * P⁻¹ ∧
      (P * e * P⁻¹)ᴴ * A = A * (1 - P * e * P⁻¹) := by sorry
