-- Prove2me | Theorems.Thm_P2M_PI_ProdFormulaE_Tr_LocFam___tmul_c045d1bf3d1e
-- name    : P2M_PI_ProdFormulaE_Tr_LocFam___tmul_c045d1bf3d1e
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:11:52.05243+00:00
-- url     : https://prove2.me/theorems/6ddac554-1d0f-4e22-803b-04dbc237f56b
-- title:
--   P2 M PI Prod Formula E Tr Loc Fam   tmul c045d1bf3d1e: P2 M PI Prod Formula E Tr Loc Fam   tmul c045d1bf3d1e
-- statement:
--   The P2 M PI Prod Formula E Tr Loc Fam   tmul c045d1bf3d1e construction uses the P2 M PI Prod Formula E Tr Loc Fam   tmul c045d1bf3d1e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProductFormulaHaar/TrBase.lean#L35-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProductFormulaHaar/TrBase.lean#L35-L37

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_TrBase
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IsDedekindDomain NumberField TensorProduct ValuativeRel
open PI PI.ProdFormulaE PI.ProdFormulaE.Tr
attribute [instance] LocFam.fld LocFam.vr LocFam.top LocFam.lf LocFam.cz LocFam.alg LocFam.fin
variable {F : Type} [Field F] [NumberField F] {ℓ : ℕ} [Fact ℓ.Prime] {ι : Type}

theorem P2M_PI_ProdFormulaE_Tr_LocFam___tmul_c045d1bf3d1e (D : LocFam F ℓ ι) (c : ℚ_[ℓ]) (x : F) (i : ι) :
    D.Φ (c ⊗ₜ x) i = algebraMap ℚ_[ℓ] (D.K i) c * D.ιF i x := by sorry

alias «PI».«ProdFormulaE».«Tr».«LocFam».«Φ_tmul» := P2M_PI_ProdFormulaE_Tr_LocFam___tmul_c045d1bf3d1e
