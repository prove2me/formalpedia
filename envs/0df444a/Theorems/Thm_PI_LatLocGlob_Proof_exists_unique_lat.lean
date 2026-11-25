-- Prove2me | Theorems.Thm_PI_LatLocGlob_Proof_exists_unique_lat
-- name    : PI.LatLocGlob.Proof.exists_unique_lat
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:34:14.168001+00:00
-- url     : https://prove2.me/theorems/5b4d147b-3b61-475f-8a96-c5d1570e0dae
-- title:
--   Proof: exists unique lat
-- statement:
--   The Proof construction uses the exists unique lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalGlobalLattice/ExistsSmulMemOfLocal.lean#L179-L285
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalGlobalLattice/ExistsSmulMemOfLocal.lean#L179-L285

import Definitions.Def_Formalism_PeriodIntegrals_LatLocGlob
import Definitions.Def_Lemmata_GeneralBFactThirdBisAlt_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalGlobalLattice_ExistsSmulMemOfLocal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LatLocGlob PI.LatLocGlob.Proof
open PI.LatLocGlob
variable {R K V : Type} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

theorem PI.LatLocGlob.Proof.exists_unique_lat (L0 : Submodule R V) (hL0 : IsFullLat K L0) (M : Ideal R → Set V)
    (hM : ∀ p : Ideal R, p.IsMaximal → ∃ N : Submodule R V, IsFullLat K N ∧ M p = loc p N)
    (hfin : Set.Finite {p : Ideal R | p.IsMaximal ∧ M p ≠ loc p L0}) :
    ∃! L : Submodule R V, IsFullLat K L ∧ ∀ p : Ideal R, p.IsMaximal → loc p L = M p := by sorry
