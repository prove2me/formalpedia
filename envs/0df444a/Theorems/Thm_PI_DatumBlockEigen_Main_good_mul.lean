-- Prove2me | Theorems.Thm_PI_DatumBlockEigen_Main_good_mul
-- name    : PI.DatumBlockEigen.Main.good_mul
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:26:59.11378+00:00
-- url     : https://prove2.me/theorems/6d21f10c-caa1-44e3-a0ff-cc0f7de0cf8e
-- title:
--   Main: good mul
-- statement:
--   The Main construction uses the good mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BlockEigenvalues/PhiUZero.lean#L150-L192
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BlockEigenvalues/PhiUZero.lean#L150-L192

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DatumBlockEigen
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LemmaU
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BlockEigenvalues_IsIntInvOfUnit
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BlockEigenvalues_PhiUZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PI PI.DatumBlockEigen PI.DatumBlockEigen.Main
open PI.DatumBlockEigen.Unit Formalism.DoubleCosetMeasures
variable {F : Type} [Field F] {a t : ℕ}
variable (O : Subring F) (ϖ : F) (J' : Subgroup (GL (Fin a) F))
variable {O ϖ J'}

theorem PI.DatumBlockEigen.Main.good_mul (hϖ : ϖ ∈ O) (hϖ0 : ϖ ≠ 0) (hL : IsLocalAt O ϖ) (hK : congSub O ϖ a ≤ J')
    (hJ : J' ≤ GLint O a) (N : Matrix (Fin a ⊕ Fin t) (Fin a ⊕ Fin t) F) (n : J')
    (hn : ((n : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) = N.toBlocks₁₁)
    (h12 : ∀ i j, N.toBlocks₁₂ i j ∈ O) (h21 : N.toBlocks₂₁ ∈ IIset O ϖ)
    (h22 : ∀ i j, N.toBlocks₂₂ i j ∈ O) (x : Matrix (Fin a ⊕ Fin t) (Fin a) F) (m : J')
    (hm : ((m : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) = toRows₁ x)
    (hx : toRows₂ x ∈ IIset O ϖ) :
    ∃ g : J', ((g : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) = toRows₁ (N * x) ∧
      toRows₂ (N * x) ∈ IIset O ϖ ∧
      ∃ U : J', (U : GL (Fin a) F) ∈ congSub O ϖ a ∧ g = n * m * U := by sorry
