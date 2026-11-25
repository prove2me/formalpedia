-- Prove2me | Theorems.Thm_P2M_PI_MirabolicIndex__card_GL_eq_7b3d39d97820
-- name    : P2M_PI_MirabolicIndex__card_GL_eq_7b3d39d97820
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:56:37.416794+00:00
-- url     : https://prove2.me/theorems/9bd320fc-0959-4c71-bb00-b6948f9b49cb
-- title:
--   P2 M PI Mirabolic Index  card GL eq 7b3d39d97820: P2 M PI Mirabolic Index  card GL eq 7b3d39d97820
-- statement:
--   The P2 M PI Mirabolic Index  card GL eq 7b3d39d97820 construction uses the P2 M PI Mirabolic Index  card GL eq 7b3d39d97820 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MirabolicIndex/RowMulOfMirab.lean#L126-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MirabolicIndex/RowMulOfMirab.lean#L126-L136

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

theorem P2M_PI_MirabolicIndex__card_GL_eq_7b3d39d97820 (n : ℕ) :
    Nat.card (GL (Fin (n + 1)) k) = (Fintype.card k ^ (n + 1) - 1) *
      Nat.card {h : GL (Fin (n + 1)) k // IsMirab (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k)} := by sorry

alias «PI».«MirabolicIndex₂».«card_GL_eq» := P2M_PI_MirabolicIndex__card_GL_eq_7b3d39d97820
