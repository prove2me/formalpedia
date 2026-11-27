-- Prove2me | Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_Pi_of_fix
-- name    : PI.VolSemiDirect.W.PG.Dat.Pi_of_fix
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T13:48:28.639619+00:00
-- url     : https://prove2.me/theorems/8a942f70-2b96-4756-b687-e742146735db
-- title:
--   Dat: Pi of fix
-- statement:
--   The Dat construction uses the Pi of fix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/HermitianIsotropicProjComplement.lean#L123-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/HermitianIsotropicProjComplement.lean#L123-L142

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

theorem PI.VolSemiDirect.W.PG.Dat.Pi_of_fix (H : D.Hyp) {S : (n → A) →ₗ[A] (n → A)} (hS : D.FixEZ S)
    (hf : ∀ a, S (D.f a) = D.f a) (hU : D.Uni S) (v : n → A) : D.Pi S v = S v := by sorry
