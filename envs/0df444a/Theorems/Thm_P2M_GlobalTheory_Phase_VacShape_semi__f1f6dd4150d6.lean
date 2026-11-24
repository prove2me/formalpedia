-- Prove2me | Theorems.Thm_P2M_GlobalTheory_Phase_VacShape_semi__f1f6dd4150d6
-- name    : P2M_GlobalTheory_Phase_VacShape_semi__f1f6dd4150d6
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T21:54:25.125029+00:00
-- url     : https://prove2.me/theorems/d1fcd741-bd75-464a-8343-0151449f3a98
-- title:
--   P2 M Global Theory Phase Vac Shape semi  f1f6dd4150d6: P2 M Global Theory Phase Vac Shape semi  f1f6dd4150d6
-- statement:
--   The P2 M Global Theory Phase Vac Shape semi  f1f6dd4150d6 construction uses the P2 M Global Theory Phase Vac Shape semi  f1f6dd4150d6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SelfDualVacuumGaussianShapeRootOfUnityPhases.lean#L41-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SelfDualVacuumGaussianShapeRootOfUnityPhases.lean#L41-L44

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IntMIffInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsExOfPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SelfDualVacuumGaussianShapeRootOfUnityPhases
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW GlobalTheory.Phase
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.Phase GlobalTheory.Phase.VacShape
open GlobalTheory.SW.Vac
variable {κ ι : Type} [Fintype κ] [Fintype ι] [DecidableEq ι]
  {A : AddSubgroup (Matrix κ ι ℚ × Matrix κ ι ℚ)} {ε : Matrix κ ι ℚ × Matrix κ ι ℚ → ℂ}
  {φ : Matrix κ ι ℚ → ℂ}
omit [DecidableEq ι]

theorem P2M_GlobalTheory_Phase_VacShape_semi__f1f6dd4150d6 (h : VacS A ε φ) : ∀ y ∈ A, ∀ y' ∈ A,
    ε (y + y') = ε y * ε y' * ex (pr y.1 y'.2 - pr y'.1 y.2) := by sorry

alias «GlobalTheory».«Phase».«VacShape».«semi'» := P2M_GlobalTheory_Phase_VacShape_semi__f1f6dd4150d6
