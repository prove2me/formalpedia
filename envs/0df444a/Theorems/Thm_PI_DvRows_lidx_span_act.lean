-- Prove2me | Theorems.Thm_PI_DvRows_lidx_span_act
-- name    : PI.DvRows.lidx_span_act
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:22:25.810795+00:00
-- url     : https://prove2.me/theorems/de404290-7f9a-4e43-b391-76d979eb47df
-- title:
--   Dv Rows: lidx span act
-- statement:
--   The Dv Rows construction uses the lidx span act property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionRows/LatticeFinitelyGenerated.lean#L432-L492
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionRows/LatticeFinitelyGenerated.lean#L432-L492

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
variable {K : Type} [Field K] [NumberField K]
variable {V : Type*} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem PI.DvRows.lidx_span_act (w : HeightOneSpectrum (𝓞 K)) {d : ℕ} (y : Fin d → V)
    (hy : LinearIndependent K y) (P : Matrix (Fin d) (Fin d) K) (hP : P.det ≠ 0) :
    lidx w.asIdeal (Submodule.span (𝓞 K) (Set.range y))
      (Submodule.span (𝓞 K) (Set.range fun j => ∑ k, P k j • y k)) = vAdd w P.det := by sorry
