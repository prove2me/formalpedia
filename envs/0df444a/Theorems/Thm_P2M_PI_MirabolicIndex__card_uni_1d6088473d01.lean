-- Prove2me | Theorems.Thm_P2M_PI_MirabolicIndex__card_uni_1d6088473d01
-- name    : P2M_PI_MirabolicIndex__card_uni_1d6088473d01
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:12:24.160837+00:00
-- url     : https://prove2.me/theorems/b5c12567-aedf-438f-bf79-ff5f23162dcb
-- title:
--   P2 M PI Mirabolic Index  card uni 1d6088473d01: P2 M PI Mirabolic Index  card uni 1d6088473d01
-- statement:
--   The P2 M PI Mirabolic Index  card uni 1d6088473d01 construction uses the P2 M PI Mirabolic Index  card uni 1d6088473d01 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MirabolicIndex/RowMulOfMirab.lean#L217-L222
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MirabolicIndex/RowMulOfMirab.lean#L217-L222

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_MirabIndex
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MirabolicIndex_RowMulOfMirab
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.MirabolicIndex₂
open Finset Matrix PI.MirabIndex
variable {k : Type} [Field k] [Fintype k]

theorem P2M_PI_MirabolicIndex__card_uni_1d6088473d01 (n : ℕ) :
    Nat.card {u : GL (Fin (n + 1)) k // IsUniU (u : Matrix (Fin (n + 1)) (Fin (n + 1)) k)} =
      Fintype.card k ^ ((n + 1) * n / 2) := by sorry

alias «PI».«MirabolicIndex₂».«card_uni» := P2M_PI_MirabolicIndex__card_uni_1d6088473d01
