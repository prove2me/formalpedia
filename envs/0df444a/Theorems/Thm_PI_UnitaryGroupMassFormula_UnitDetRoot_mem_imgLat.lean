-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UnitDetRoot_mem_imgLat
-- name    : PI.UnitaryGroupMassFormula.UnitDetRoot.mem_imgLat
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:33:35.655823+00:00
-- url     : https://prove2.me/theorems/8993be07-9ffd-41dc-8cf0-bd336234369c
-- title:
--   Unit Det Root: mem img Lat
-- statement:
--   The Unit Det Root construction uses the mem img Lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitDeterminantRoot/NsmulRelIdxMem.lean#L95-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitDeterminantRoot/NsmulRelIdxMem.lean#L95-L100

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitDeterminantRoot_GlobalLUnit
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitDeterminantRoot_NsmulRelIdxMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UnitDetRoot
open PI

theorem PI.UnitaryGroupMassFormula.UnitDetRoot.mem_imgLat {m : Type} {δ : (m → ℂ) ≃ₗ[ℂ] (m → ℂ)} {Λ : AddSubgroup (m → ℂ)} {z : m → ℂ} :
    z ∈ UnitDetRootDefs.imgLat (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λ ↔ δ.symm z ∈ Λ := by sorry
