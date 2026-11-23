-- Prove2me | Theorems.Thm_PI_LevelKSplit_W_SemiA_S_e
-- name    : PI.LevelKSplit.W.SemiA.S_e
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:32:48.049938+00:00
-- url     : https://prove2.me/theorems/2c18afec-1356-4c4a-8c93-697fc0102190
-- title:
--   Semi A: S e
-- statement:
--   The Semi A construction uses the S e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/SemiAlg.lean#L130-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/SemiAlg.lean#L130-L136

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_HermitianIsotropicProjComplement
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FundamentalEquivalence_LevelIntersectParabolic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_SemiAlg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LevelKSplit PI.LevelKSplit.W PI.LevelKSplit.W.SemiA
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
open scoped TensorProduct
variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) {r : ℕ} (P : Frame E M r) (T : F)
variable {R σ J P T}

theorem PI.LevelKSplit.W.SemiA.S_e {g : HA R σ J} (hg : g ∈ Ssub R σ J P) (b : Fin r) :
    lin R σ J g (ratV (F := F) R (P.e b)) - ratV (F := F) R (P.e b) ∈
      spanR (F := F) R P.e {a | a < b} := by sorry
