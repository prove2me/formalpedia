-- Prove2me | Theorems.Thm_PI_NcVal_OmVc1_gram_entry
-- name    : PI.NcVal.OmVc1.gram_entry
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T10:10:25.266273+00:00
-- url     : https://prove2.me/theorems/0e6787e8-86de-512f-a3d9-d99fea17b621
-- title:
--   Om Vc1: gram entry
-- statement:
--   The Om Vc1 construction uses the gram entry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ValuationLocalVolumes/GramMulTupHolds.lean#L11-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ValuationLocalVolumes/GramMulTupHolds.lean#L11-L28

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SiegelWeilVolume_AddEquivAddHaarCharEqOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ValuationLocalVolumes_GramMulTupHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.NcVal PI.NcVal.OmVc1
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.DegenerateSiegelWeil.Scale
open scoped TensorProduct

theorem PI.NcVal.OmVc1.gram_entry {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R]
    [Algebra F R] (σ : E →ₐ[F] E) (n M : ℕ) (J : Matrix (Fin M) (Fin M) E)
    (D : Matrix (Fin n) (Fin n) (R ⊗[F] E)) (X : Fin n → Fin M → R ⊗[F] E) (a b : Fin n) :
    gramR R σ J (mulTup D X) a b = (conjT R σ D * gramR R σ J X * D) a b := by sorry
