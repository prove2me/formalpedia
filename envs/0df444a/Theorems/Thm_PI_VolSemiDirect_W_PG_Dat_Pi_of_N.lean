-- Prove2me | Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_Pi_of_N
-- name    : PI.VolSemiDirect.W.PG.Dat.Pi_of_N
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T13:48:27.951932+00:00
-- url     : https://prove2.me/theorems/7c42217e-18b7-43a2-9100-81c6faf3dd05
-- title:
--   Dat: Pi of N
-- statement:
--   The Dat construction uses the Pi of N property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/HermitianIsotropicProjComplement.lean#L158-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/HermitianIsotropicProjComplement.lean#L158-L166

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

theorem PI.VolSemiDirect.W.PG.Dat.Pi_of_N (H : D.Hyp) {S : (n → A) →ₗ[A] (n → A)}
    (hN : ∀ v, (∀ a, D.h (D.e a) v = 0) → S v - v ∈ Submodule.span A (Set.range D.e))
    (v : n → A) : D.Pi S v = v := by sorry
