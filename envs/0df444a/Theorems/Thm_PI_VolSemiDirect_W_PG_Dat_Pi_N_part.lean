-- Prove2me | Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_Pi_N_part
-- name    : PI.VolSemiDirect.W.PG.Dat.Pi_N_part
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T13:48:24.358553+00:00
-- url     : https://prove2.me/theorems/e2414ddc-67ee-4457-8ebc-6eef2c4c4ff3
-- title:
--   Dat: Pi N part
-- statement:
--   The Dat construction uses the Pi N part property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/HermitianIsotropicProjComplement.lean#L168-L180
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/HermitianIsotropicProjComplement.lean#L168-L180

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ProjGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_HermitianIsotropicProjComplement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolSemiDirect PI.VolSemiDirect.W PI.VolSemiDirect.W.PG
open Formalism.UG
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] {r : ℕ}
open PI.VolSemiDirect.W.PG.Dat
variable {D : Dat A n r}

theorem PI.VolSemiDirect.W.PG.Dat.Pi_N_part (H : D.Hyp) {S Si : (n → A) →ₗ[A] (n → A)} (hS : D.FixEZ S)
    (hSi : D.FixEZ Si) (hUi : D.Uni Si) (hSSi : ∀ v, S (Si v) = v) (v : n → A)
    (hv : ∀ a, D.h (D.e a) v = 0) :
    S (D.Pi Si v) - v ∈ Submodule.span A (Set.range D.e) := by sorry
