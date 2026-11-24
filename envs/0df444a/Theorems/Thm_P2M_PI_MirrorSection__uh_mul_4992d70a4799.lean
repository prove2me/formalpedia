-- Prove2me | Theorems.Thm_P2M_PI_MirrorSection__uh_mul_4992d70a4799
-- name    : P2M_PI_MirrorSection__uh_mul_4992d70a4799
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T14:55:53.8958+00:00
-- url     : https://prove2.me/theorems/2c100e3e-979b-4b29-9986-71eb69b01c0a
-- title:
--   P2 M PI Mirror Section  uh mul 4992d70a4799: P2 M PI Mirror Section  uh mul 4992d70a4799
-- statement:
--   The P2 M PI Mirror Section  uh mul 4992d70a4799 construction uses the P2 M PI Mirror Section  uh mul 4992d70a4799 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MirrorDecomposition/HpkRowEsI.lean#L31-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MirrorDecomposition/HpkRowEsI.lean#L31-L37

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MirrorDecomposition_HpkRowEsI
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
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2
variable {k r : ℕ}

theorem P2M_PI_MirrorSection__uh_mul_4992d70a4799 {a b : B.Mat k r} (ha : a ∈ UH (Hpk k r)) (hb : b ∈ UH (Hpk k r)) : a * b ∈ UH (Hpk k r) := by sorry

alias «PI».«MirrorSection₂».«uh_mul» := P2M_PI_MirrorSection__uh_mul_4992d70a4799
