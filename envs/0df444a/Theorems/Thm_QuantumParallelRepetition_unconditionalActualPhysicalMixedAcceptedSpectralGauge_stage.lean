-- Prove2me | Theorems.Thm_QuantumParallelRepetition_unconditionalActualPhysicalMixedAcceptedSpectralGauge_stage
-- name    : QuantumParallelRepetition.unconditionalActualPhysicalMixedAcceptedSpectralGauge_stage
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-11T18:59:06.111415+00:00
-- url     : https://prove2.me/theorems/24546d86-69b6-4d1f-8398-ed2e0dab6a1b
-- title:
--   A local change of spectral basis turns the raw accepted stage into the coherent mixed state
-- statement:
--   Fix a phase count $B$, a grid size $N$, a local dimension $d$, a harmonic count $m$, a width $w > 0$ with $N > 0$, and bipartite unit vectors $\xi, \zeta$. Let $U_A$ be the selected-copy lift of Alice's history spectral copy unitary for $\xi$, and $U_B$ the selected-copy lift of the inverse of Bob's history copy basis for $\zeta$; both act on the selected-copy local index $(\text{phase} \times \text{dimension}) \times \text{grid} \cdot \text{harmonic}$. The theorem states that
--   $$
--   (U_A \otimes U_B)\;\big|\mathrm{raw}_w(\xi,\zeta)\big\rangle \;=\; \big|\mathrm{coh}_w(\xi,\zeta)\big\rangle,
--   $$
--   where the raw accepted mixed stage has amplitudes given by the EPR phase amplitude times the rational accepted-outcome amplitude times the embezzlement amplitude, and the right-hand side is the public-bucket coherent mixed state at the same parameters. The two states thus differ only by a product unitary — a purely local change of spectral gauge.
-- source:
--   OpenAI, ten-proofs, QuantumParallelRepetition.lean, https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/QuantumParallelRepetition.lean#L61684-L61749

import Definitions.Def_quantum_parallel_repetition_game
import Definitions.Def_qpr_core_25
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Submonoid.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Notation.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.Unitary
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.FunLike.Equiv
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.SetLike.Basic
import Mathlib.Data.Sigma.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Topology.Defs.Filter

open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
attribute [local instance] Classical.propDecidable

theorem QuantumParallelRepetition.unconditionalActualPhysicalMixedAcceptedSpectralGauge_stage
    {B N d m : ℕ} {w : ℝ}
    (width : 0 < w) (grid : 0 < N)
    (ξ ζ : BipartiteUnitVector d) :
    toLp 2
      ((((unconditionalActualCleanedSelectedStageSpectralUnitary
            (B := B) (m := m)
            (dSVUniformDensityAliceHistorySpectralCopy
              (N := N) ξ) :
            Matrix (UnconditionalSelectedCopyLocalIndex B d N m)
              (UnconditionalSelectedCopyLocalIndex B d N m) ℂ) ⊗ₖ
          (unconditionalActualCleanedSelectedStageSpectralUnitary
            (B := B) (m := m)
            ((dSVUniformDensityBobHistoryCopyBasis
              (N := N) ζ)⁻¹) :
            Matrix (UnconditionalSelectedCopyLocalIndex B d N m)
              (UnconditionalSelectedCopyLocalIndex B d N m) ℂ)).mulVec
        (ofLp (unconditionalActualPhysicalMixedAcceptedRawStage
          (B := B) (m := m) w ξ ζ)))) =
      dSVDensityRationalPublicBucketPhysicalCoherentMixedState
        (N := N) (B := B) w m ξ ζ := by sorry
