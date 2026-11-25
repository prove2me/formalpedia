-- Prove2me | Theorems.Thm_PI_AlgValsFin_W_exists_nbhd
-- name    : PI.AlgValsFin.W.exists_nbhd
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:23:08.061336+00:00
-- url     : https://prove2.me/theorems/adb57f8f-bdfe-4f24-8836-dfab9e9b8b8f
-- title:
--   W: exists nbhd
-- statement:
--   The W construction uses the exists nbhd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AlgebraicValuesFinite/InvMemUFin.lean#L54-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AlgebraicValuesFinite/InvMemUFin.lean#L54-L112

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_ClassSame
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_InvMemUFin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero Neutral.B1 Topology
open PI PI.AlgValsFin PI.AlgValsFin.W
variable {L : Type} [Field L] [NumberField L]

theorem PI.AlgValsFin.W.exists_nbhd (W : Set (Ideles L)) (hW : IsOpen W) (h1 : (1 : Ideles L) ∈ W) :
    ∃ (S : Finset (HeightOneSpectrum (𝓞 L))) (n : ℕ), ∀ x ∈ UFin L,
      (∀ v ∈ S, Valued.v ((x : AdeleRing (𝓞 L) L).2 v - 1) ≤ exp (-(n : ℤ))) → x ∈ W := by sorry
