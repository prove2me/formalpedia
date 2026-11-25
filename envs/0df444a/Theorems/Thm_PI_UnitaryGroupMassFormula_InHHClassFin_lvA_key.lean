-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_InHHClassFin_lvA_key
-- name    : PI.UnitaryGroupMassFormula.InHHClassFin.lvA_key
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T12:42:35.949796+00:00
-- url     : https://prove2.me/theorems/62cf329e-c26a-40f7-9bba-57391adab64f
-- title:
--   In HHClass Fin: lv A key
-- statement:
--   The In HHClass Fin construction uses the lv A key property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianClassFiniteness/LevelA.lean#L22-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianClassFiniteness/LevelA.lean#L22-L42

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelaf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianClassFiniteness_LevelA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix IsDedekindDomain
open scoped TensorProduct
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.InHHClassFin
variable {R : Type} [CommRing R] (S : Subring R) {n : ℕ}

theorem PI.UnitaryGroupMassFormula.InHHClassFin.lvA_key {ι : Type} [Fintype ι] [DecidableEq ι] (LA : Submodule S (Fin n → R))
    (c₁ c₂ c g : R)
    (h₁ : ∀ y ∈ LA, ∀ i, c₁ * y i ∈ S) (h₂ : ∀ y : Fin n → R, (∀ i, y i ∈ S) → c₂ • y ∈ LA)
    (P : Matrix (Fin n) ι R) (Q : Matrix ι (Fin n) R) (hPQ : P * Q = 1)
    (hP : ∀ i j, (c • P) i j ∈ S) (hQ : ∀ i j, (c • Q) i j ∈ S)
    (N : Matrix ι ι R) (hN : ∀ i j, N i j ∈ S) (u : Matrix ι ι R)
    (hu : u = 1 + (g * c₂ * c * c * c₁) • N) :
    ∀ y ∈ LA, ∃ z ∈ LA, (P * u * Q - 1) *ᵥ y = g • z := by sorry
