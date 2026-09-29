-- Prove2me | Theorems.Thm_QuantumParallelRepetition_exists_proofDSVDensityRationalPublicBucketPhysicalQuantitativeMixedPrefixCleanup_sq
-- name    : QuantumParallelRepetition.exists_proofDSVDensityRationalPublicBucketPhysicalQuantitativeMixedPrefixCleanup_sq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-11T10:30:18.569257+00:00
-- url     : https://prove2.me/theorems/4cbdcf8f-c7db-4c0f-8d0e-2bced2bf3e28
-- title:
--   Phase-averaged prefix cleanup for logarithmic rank buckets
-- statement:
--   Specialize the bucket cleanup to the logarithmic rank bucketing: with $B\ge 1$ phases and fineness $Q\ge 1$, rank $r>0$ is assigned the label $\big\lfloor(\lfloor Q\log r\rfloor+\text{phase})/B\big\rfloor$, rank $0$ gets its own label, and the representative of a label is the smallest rank in its fiber. Then for every $N\ge 1$ and $\varepsilon>0$ there are $n\ge 1$ and unitary families $A,C:\{1,\dots,B\}\times(\mathbb N\cup\{\ast\})\to\mathrm U(Nn)$ such that for all ranks $r,s\in\{0,\dots,N\}$ the phase-averaged squared cleanup error obeys $$\frac1B\sum_{\text{phase}}\big\|(A\otimes C)|\Psi_{\min(r,s)}\rangle-\sqrt r\,|\mu_{Nn}\rangle\big\|^{2}\le 2|r-s|+4r\varepsilon^{2}+16r\big(e^{(B+1)/Q}-1\big)+8\Big(\big(\tfrac QB+1\big)|r-s|+\frac{\min(r,s)}{B}\Big).$$ The point of averaging over phases is that the bucket-mismatch penalty, which is $O(1)$ for a single phase, becomes proportional to the rank gap plus $1/B$.
-- source:
--   OpenAI, ten-proofs, QuantumParallelRepetition.lean, https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/QuantumParallelRepetition.lean#L44583-L44761

import Definitions.Def_quantum_parallel_repetition_game
import Definitions.Def_qpr_core_23
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Action.Pi
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.Group.Submonoid.Defs
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Notation.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.Algebra.Order.GroupWithZero.Unbundled.Basic
import Mathlib.Algebra.Order.GroupWithZero.Unbundled.Defs
import Mathlib.Algebra.Order.IsBotOne
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Init
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.SetLike.Basic
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Order.Basic
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Lattice
import Mathlib.Order.RelClasses
import Mathlib.Tactic.CancelDenoms.Core
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.Linarith.Preprocessing
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Positivity.Core
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common
import Mathlib.Topology.Defs.Filter

open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

theorem
    QuantumParallelRepetition.exists_proofDSVDensityRationalPublicBucketPhysicalQuantitativeMixedPrefixCleanup_sq
    {N B : ℕ} (grid : 0 < N) (phases : 0 < B)
    {Q : ℕ} (fine : 0 < Q)
    (ε : ℝ) (precision : 0 < ε) :
    ∃ n : ℕ, 0 < n ∧
      ∃ A C : Fin B → Option ℕ →
          Matrix.unitaryGroup (Fin (N * n)) ℂ,
        ∀ (r s : Fin (N + 1)),
          (∑ phase : Fin B,
            dSVDensityRationalPublicLogRankPhaseWeight B phase *
              ‖localUnitaryAction
                  (A phase
                    (dSVDensityRationalPublicLogRankBucket
                      Q phase r))
                  (C phase
                    (dSVDensityRationalPublicLogRankBucket
                      Q phase s))
                  (dSVDensityRationalMixedCanonicalPrefixPureHarmonicTensor
                    n (dSVCanonicalFailurePrefix
                      (dSVDensityRationalPublicBucketPhysicalCommonRank
                        r s))) -
                Real.sqrt (r.val : ℝ) •
                  embezzlementState (N * n)‖ ^ 2) ≤
            2 * |(r.val : ℝ) - (s.val : ℝ)| +
            4 * (r.val : ℝ) * ε ^ 2 +
            16 * (r.val : ℝ) *
              (Real.exp (((B : ℝ) + 1) / (Q : ℝ)) - 1) +
            8 * (((Q : ℝ) / (B : ℝ) + 1) *
              |(r.val : ℝ) - (s.val : ℝ)| +
              min (r.val : ℝ) (s.val : ℝ) / (B : ℝ)) := by sorry
