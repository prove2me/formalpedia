-- Prove2me | Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_h_e_S
-- name    : PI.VolSemiDirect.W.PG.Dat.h_e_S
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:18:40.189789+00:00
-- url     : https://prove2.me/theorems/8a581176-524c-4116-9ac1-96bd30bd363d
-- title:
--   Dat: h e S
-- statement:
--   The Dat construction uses the h e S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/HermitianIsotropicProjComplement.lean#L48-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/HermitianIsotropicProjComplement.lean#L48-L51

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

theorem PI.VolSemiDirect.W.PG.Dat.h_e_S {S : (n → A) →ₗ[A] (n → A)} (hS : D.FixEZ S) (hU : D.Uni S) (b : Fin r)
    (w : n → A) : D.h (D.e b) (S w) = D.h (D.e b) w := by sorry
