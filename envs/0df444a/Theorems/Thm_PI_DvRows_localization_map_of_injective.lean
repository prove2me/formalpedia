-- Prove2me | Theorems.Thm_PI_DvRows_localization_map_of_injective
-- name    : PI.DvRows.localization_map_of_injective
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:29:23.330343+00:00
-- url     : https://prove2.me/theorems/80c1cf35-b97e-4d3d-81da-5cecaf348825
-- title:
--   Dv Rows: localization map of injective
-- statement:
--   The Dv Rows construction uses the localization map of injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionRows/LatticeFinitelyGenerated.lean#L270-L283
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionRows/LatticeFinitelyGenerated.lean#L270-L283

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_Pieces
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndexDeterminant_NegLogValuation
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_LatticeFinitelyGenerated
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.DvRows
open NumberField IsDedekindDomain Formalism.BasicNotions PI.Dv
open Formalism.HermitianLatticesTheory
variable {R : Type*} [CommRing R] {W W' : Type*} [AddCommGroup W] [Module R W]
  [AddCommGroup W'] [Module R W']

theorem PI.DvRows.localization_map_of_injective (p : Ideal R) [p.IsPrime] (f : W →ₗ[R] W') (hf : Function.Injective f)
    (hsat : ∀ (s : R) (y : W'), s ∈ p.primeCompl → s • y ∈ LinearMap.range f →
      y ∈ LinearMap.range f)
    (A : Submodule R W) : localization₂ p (A.map f) = (localization₂ p A).map f := by sorry
