-- Prove2me | Theorems.Thm_PI_ProdFormulaE_Tr_LocFam_denseDiag
-- name    : PI.ProdFormulaE.Tr.LocFam.denseDiag
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:36:23.235557+00:00
-- url     : https://prove2.me/theorems/5ca9c6e4-3df4-5478-9106-e4684e2c94e0
-- title:
--   Loc Fam: dense Diag
-- statement:
--   The Loc Fam construction uses the dense Diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProductFormulaHaar/T2SpaceOfIsValuativeTopology.lean#L98-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProductFormulaHaar/T2SpaceOfIsValuativeTopology.lean#L98-L113

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_TrBase
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_T2SpaceOfIsValuativeTopology
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IsDedekindDomain NumberField TensorProduct ValuativeRel Filter Topology
open PI PI.ProdFormulaE PI.ProdFormulaE.Tr
variable {F : Type} [Field F] [NumberField F]
variable {ℓ : ℕ} [Fact ℓ.Prime] {ι : Type}

theorem PI.ProdFormulaE.Tr.LocFam.denseDiag [Finite ι] (D : LocFam F ℓ ι) (hP : Function.Injective D.P) :
    DenseRange (fun x : F => fun i => D.ιF i x) := by sorry
