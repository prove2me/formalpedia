-- Prove2me | Theorems.Thm_QuantumParallelRepetition_unconditionalActualCanonicalFullSource_eq_rawSelectedStage
-- name    : QuantumParallelRepetition.unconditionalActualCanonicalFullSource_eq_rawSelectedStage
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-11T19:24:03.582333+00:00
-- url     : https://prove2.me/theorems/a1a085e3-4d2a-4b41-b966-d5eaafdd5ad3
-- title:
--   The canonical fixed-source matched branch factors as raw selected stage tensor retained work
-- statement:
--   Fix finitely many scales $S$, a phase count $B$, a grid size $N$, a local dimension $d$, a
--   number of rounds $L$ and an embezzlement parameter $m$. Let $\mathrm{width} : \mathrm{Fin}\,S \to
--   \mathbb{R}$ assign a width to each scale, let $\mathrm{schedule} : \mathrm{Fin}\,L \to
--   \mathrm{Fin}\,S$ say which scale is used at each round, let $\xi, \zeta$ be unit vectors of a
--   bipartite system of local dimension $d$, and fix a round $j \in \mathrm{Fin}\,L$.
--
--   At round $j$ the matched branch of the cleaned bilateral state is written in coordinates that
--   bundle together a phase register, a local history, and an embezzlement register. Transporting it
--   along the inverse of the multiscale phase-index equivalence at scale $\mathrm{schedule}(j)$ — the
--   reindexing performed by the source-physical cleaned full bilateral state isometry — turns it into
--   a product of two independent factors:
--
--   $$
--   \mathcal{I}_{j}\bigl(\mathrm{MatchedBranch}_{j}\bigr)
--     = \mathrm{RawSelectedStage}\bigl(\mathrm{width}(\mathrm{schedule}\,j),\ \xi,\ \zeta\bigr)
--       \otimes \mathrm{RetainedWork}_{j},
--   $$
--
--   where the first factor is the canonical raw selected physical stage at the width of the scale
--   scheduled for round $j$ and depends only on that round's data, and the second is the retained work
--   of the selected copy, carrying the common prefix, the independent shared state on the rounds after
--   $j$, and the retained phase tail. In other words, once the phase index is unpacked, the round-$j$
--   matched branch of the full source state is exactly a tensor product of the selected stage with the
--   work the protocol keeps aside, with no residual correlation between the two.
-- source:
--   OpenAI, ten-proofs, QuantumParallelRepetition.lean, https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/QuantumParallelRepetition.lean#L61837-L61917

import Definitions.Def_quantum_parallel_repetition_game
import Definitions.Def_qpr_core_25
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Ring.CompTypeclasses
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Star.Basic
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.AlgebraicTopology.SimplexCategory.Defs
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.FunLike.Equiv
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Data.Sigma.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common
import Mathlib.Topology.Defs.Filter

open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

theorem QuantumParallelRepetition.unconditionalActualCanonicalFullSource_eq_rawSelectedStage
    {S B N d L m : ℕ}
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) (j : Fin L) :
    unconditionalSourcePhysicalCleanedFullBilateralStateIsometry
        (unconditionalActualMultiscalePhaseIndexEquiv
          (schedule j)).symm j
        (unconditionalActualCanonicalFixedSourceMatchedBranch
          (B := B) (m := m) width schedule ξ ζ j) =
      unconditionalMatchedVerifierTensor
        (unconditionalActualCanonicalRawSelectedPhysicalStage
          (B := B) (m := m) (width (schedule j)) ξ ζ)
        (unconditionalSelectedCopyRetainedWork
          (N := N) width schedule ξ ζ j
          (unconditionalActualCanonicalRetainedPhaseTail
            (S := S) (B := B) j)) := by sorry
