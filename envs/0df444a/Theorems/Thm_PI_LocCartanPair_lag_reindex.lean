-- Prove2me | Theorems.Thm_PI_LocCartanPair_lag_reindex
-- name    : PI.LocCartanPair.lag_reindex
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:35:22.293597+00:00
-- url     : https://prove2.me/theorems/ddded888-8f9c-5873-b2ac-c4add9e4acfe
-- title:
--   Loc Cartan Pair: lag reindex
-- statement:
--   The Loc Cartan Pair construction uses the lag reindex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalCartanPairs/PairBaseOfLag.lean#L42-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalCartanPairs/PairBaseOfLag.lean#L42-L56

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

theorem PI.LocCartanPair.lag_reindex {ι β : Type} [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]
    (s : β ≃ ι) (A : Matrix ι ι R) (E : Matrix β β R) (hE : E * E = E)
    (hEA : Eᴴ * A.submatrix s s = A.submatrix s s * (1 - E)) :
    E.submatrix s.symm s.symm * E.submatrix s.symm s.symm = E.submatrix s.symm s.symm ∧
      (E.submatrix s.symm s.symm)ᴴ * A = A * (1 - E.submatrix s.symm s.symm) := by sorry
