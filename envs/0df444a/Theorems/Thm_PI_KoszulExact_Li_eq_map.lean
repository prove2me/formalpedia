-- Prove2me | Theorems.Thm_PI_KoszulExact_Li_eq_map
-- name    : PI.KoszulExact.Li_eq_map
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:34:16.068373+00:00
-- url     : https://prove2.me/theorems/a17c518a-b3dd-4fe5-83fa-785c1492d6d7
-- title:
--   Koszul Exact: Li eq map
-- statement:
--   The Koszul Exact construction uses the Li eq map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/KoszulExactness/ContractPowSuccMem.lean#L40-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/KoszulExactness/ContractPowSuccMem.lean#L40-L44

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_KoszulExactness_Ii
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_KoszulExactness_ContractPowSuccMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u v
open PI PI.KoszulExact
variable {R : Type u} [CommRing R] {D : ℕ}

theorem PI.KoszulExact.Li_eq_map (R : Type u) [CommRing R] (D : ℕ) (i : ℕ) :
    Li R D i = (Submodule.span R ((fun k : Fin D => (Pi.single k (1 : R) : Fin D → R)) ''
      {k : Fin D | (k : ℕ) < i})).map (ExteriorAlgebra.ι R) := by sorry
