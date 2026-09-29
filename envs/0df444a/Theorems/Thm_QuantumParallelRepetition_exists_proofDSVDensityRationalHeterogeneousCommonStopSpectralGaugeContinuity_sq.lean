-- Prove2me | Theorems.Thm_QuantumParallelRepetition_exists_proofDSVDensityRationalHeterogeneousCommonStopSpectralGaugeContinuity_sq
-- name    : QuantumParallelRepetition.exists_proofDSVDensityRationalHeterogeneousCommonStopSpectralGaugeContinuity_sq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-11T10:46:27.739747+00:00
-- url     : https://prove2.me/theorems/6298c10b-9b75-4870-8ba9-176d5e6f07ef
-- title:
--   One bucket gauge works for every stage: per-stage reset error bounded by hazard plus diagonal mass
-- statement:
--   Let $d,N,B,Q\ge 1$ and $\varepsilon>0$. There exist $n\ge 1$ and unitary families $A,C:\{1,\dots,B\}\times(\mathbb N\cup\{\ast\})\to\mathrm U(Nn)$, depending only on these parameters, such that for every stage count $L$, every width function and schedule, every pair of bipartite unit vectors $\xi,\zeta$ of local dimension $d$, and every stage $k$ with width $w=\mathrm{width}(\mathrm{schedule}(k))$, $$\big\|\mathcal R_{A,C}\big(\Phi^{\mathrm{mix}}_w\big)-\Phi^{\mathrm{tgt}}_w\big\|^{2}\le\Big(10+\tfrac{8Q}{B}\Big)H_{\times}(N,w,\xi,\zeta)+\Big(4\varepsilon^{2}+16\big(e^{(B+1)/Q}-1\big)+\tfrac8B\Big)P_{\mathrm{diag}}(w,\xi).$$ Here $\Phi^{\mathrm{mix}}_w$ is the coherent state whose $(\text{phase},i,j)$ block carries the common-rank prefix state for the pair of accepted ranks $\big(r_w(\xi,i),r_w(\zeta,j)\big)$, $\Phi^{\mathrm{tgt}}_w$ replaces each block by $\sqrt{r_w(\xi,i)}$ times the embezzlement state, $\mathcal R_{A,C}$ applies the bucket-indexed local unitaries blockwise, $H_\times$ is the projector cross-hazard between $\xi$ and $\zeta$, and $P_{\mathrm{diag}}$ is the diagonal Born success probability.
-- source:
--   OpenAI, ten-proofs, QuantumParallelRepetition.lean, https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/QuantumParallelRepetition.lean#L44878-L45132

import Definitions.Def_quantum_parallel_repetition_game
import Definitions.Def_qpr_core_23
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Action.Pi
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.Group.Submonoid.Defs
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.GroupWithZero.Unbundled.Basic
import Mathlib.Algebra.Order.GroupWithZero.Unbundled.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Ring.Defs
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
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Nat.Init
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
import Mathlib.Tactic.CancelDenoms.Core
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.Linarith.Preprocessing
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common
import Mathlib.Topology.Defs.Filter

open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

theorem
    QuantumParallelRepetition.exists_proofDSVDensityRationalHeterogeneousCommonStopSpectralGaugeContinuity_sq
    {d N B : ℕ} (grid : 0 < N) (dimension : 0 < d)
    (phases : 0 < B) {Q : ℕ} (fine : 0 < Q)
    (ε : ℝ) (precision : 0 < ε) :
    ∃ n : ℕ, 0 < n ∧
      ∃ A C : Fin B → Option ℕ →
          Matrix.unitaryGroup (Fin (N * n)) ℂ,
        ∀ {S L : ℕ}
          (width : Fin S → ℝ) (schedule : Fin L → Fin S)
          (ξ ζ : BipartiteUnitVector d) (k : Fin L),
          ‖dSVDensityRationalPublicBucketPhysicalCoherentLocalReset
              Q (width (schedule k)) ξ ζ A C
              (dSVDensityRationalPublicBucketPhysicalCoherentMixedState
                (N := N) (B := B)
                (width (schedule k)) n ξ ζ) -
            dSVDensityRationalPublicBucketPhysicalCoherentTargetState
              (N := N) (B := B)
              (width (schedule k)) n ξ ζ‖ ^ 2 ≤
            (10 + 8 * ((Q : ℝ) / (B : ℝ))) *
                dSVDensityRationalPhysicalProjectorCrossHazard
                  N (width (schedule k)) ξ ζ +
              (4 * ε ^ 2 +
                16 * (Real.exp (((B : ℝ) + 1) / (Q : ℝ)) - 1) +
                8 / (B : ℝ)) *
                dSVDensityRationalPhysicalDiagonalBornSuccess
                  grid dimension (width (schedule k)) ξ := by sorry
