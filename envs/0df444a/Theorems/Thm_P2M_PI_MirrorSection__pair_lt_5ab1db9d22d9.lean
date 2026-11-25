-- Prove2me | Theorems.Thm_P2M_PI_MirrorSection__pair_lt_5ab1db9d22d9
-- name    : P2M_PI_MirrorSection__pair_lt_5ab1db9d22d9
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:57:00.188105+00:00
-- url     : https://prove2.me/theorems/f3690f2b-2d87-589e-bec6-037dfd0c00a0
-- title:
--   P2 M PI Mirror Section  pair lt 5ab1db9d22d9: P2 M PI Mirror Section  pair lt 5ab1db9d22d9
-- statement:
--   The P2 M PI Mirror Section  pair lt 5ab1db9d22d9 construction uses the P2 M PI Mirror Section  pair lt 5ab1db9d22d9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MirrorDecomposition/MirrorDecompOf.lean#L40-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MirrorDecomposition/MirrorDecompOf.lean#L40-L48

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MirrorDecomposition_HpkRowEsI
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MirrorDecomposition_IsMonomialConjTranspose
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_Forward
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MirrorDecomposition_MirrorDecompOf
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
open PI PI.MirrorSection₂
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2 PI.StabPairsW
variable {k r : ℕ}

theorem P2M_PI_MirrorSection__pair_lt_5ab1db9d22d9 {m : ℕ} {P b u' : Matrix (Fin m) (Fin m) ℂ} (hb : b ∈ UTset m) (h : bᴴ * P * u' = P)
    (hP : IsUnit P.det) : P * u' * P⁻¹ ∈ LTset m := by sorry

alias «PI».«MirrorSection₂».«pair_lt» := P2M_PI_MirrorSection__pair_lt_5ab1db9d22d9
