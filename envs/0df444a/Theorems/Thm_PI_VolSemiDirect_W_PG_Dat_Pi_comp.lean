-- Prove2me | Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_Pi_comp
-- name    : PI.VolSemiDirect.W.PG.Dat.Pi_comp
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:35:44.450617+00:00
-- url     : https://prove2.me/theorems/0eccc9f0-fd31-5f09-8213-c9f4442b9023
-- title:
--   Dat: Pi comp
-- statement:
--   The Dat construction uses the Pi comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/HermitianIsotropicProjComplement.lean#L67-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/HermitianIsotropicProjComplement.lean#L67-L76

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

theorem PI.VolSemiDirect.W.PG.Dat.Pi_comp (H : D.Hyp) {S S' : (n → A) →ₗ[A] (n → A)} (hS : ∀ a, S (D.e a) = D.e a)
    (hS' : D.FixEZ S') (hU' : D.Uni S') (v : n → A) :
    D.Pi S (D.Pi S' v) = D.Pi (S ∘ₗ S') v := by sorry
