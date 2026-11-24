-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_kD_apply
-- name    : PositivityTheory.Rg.Cz.kD_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:09:38.563883+00:00
-- url     : https://prove2.me/theorems/6a04805d-b370-405c-9e95-43df5ad059b1
-- title:
--   Cz: k D apply
-- statement:
--   The Cz construction uses the k D apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/KugaCoordinates/KugaAbsoluteValues/KSumApply.lean#L28-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/KugaCoordinates/KugaAbsoluteValues/KSumApply.lean#L28-L31

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_KugaCoordinates_KugaAbsoluteValues_KSumApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Fin Function
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
variable {P : Type} [AddCommGroup P] [Module ℝ P] {M : Type} [AddCommGroup M] [Module ℂ M]
  [Module ℝ M] [IsScalarTower ℝ ℂ M]

theorem PositivityTheory.Rg.Cz.kD_apply (T : P →ₗ[ℝ] Module.End ℂ M) {m : ℕ} (η : P [⋀^Fin m]→ₗ[ℝ] M)
    (v : Fin (m + 1) → P) :
    kD T η v = ∑ i : Fin (m + 1), (-1 : ℤ) ^ (i : ℕ) • T (v i) (η (i.removeNth v)) := by sorry
