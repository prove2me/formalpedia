-- Prove2me | Theorems.Thm_QuantumParallelRepetition_exists_proofDSVDensityRationalHeterogeneousStoppedCommonStopGaugeErrorBound
-- name    : QuantumParallelRepetition.exists_proofDSVDensityRationalHeterogeneousStoppedCommonStopGaugeErrorBound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-11T11:51:44.289931+00:00
-- url     : https://prove2.me/theorems/c3573343-1f85-4773-9335-7ebee2edb0fd
-- title:
--   A single bucket gauge bounds the total stopped gauge error by the asynchronous mass plus a fixed additive loss
-- statement:
--   Let $d,N,B,Q\ge 1$ and $\varepsilon>0$. There exist $n\ge 1$ and unitary families $A,C:\{1,\dots,B\}\times(\mathbb N\cup\{\ast\})\to\mathrm U(Nn)$ such that, uniformly over the number of stages $L$, the widths, the schedule and the pair $\xi,\zeta$, the survival-weighted total gauge error $\sum_{k<L}\mathrm{Surv}(k)\,E_k$, where $E_k$ is the squared per-stage reset error at width $\mathrm{width}(\mathrm{schedule}(k))$, satisfies $$\sum_{k<L}\mathrm{Surv}(k)\,E_k\ \le\ \Big(10+\tfrac{8Q}{B}\Big)\,M_{\mathrm{async}}+\Big(4\varepsilon^{2}+16\big(e^{(B+1)/Q}-1\big)+\tfrac 8B\Big),$$ with $M_{\mathrm{async}}=\sum_{k<L}\mathrm{Surv}(k)\,\mathrm{async}(k)$ the stopped asynchronous mass. Note that the second term is a constant: it no longer grows with the number of stages.
-- source:
--   OpenAI, ten-proofs, QuantumParallelRepetition.lean, https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/QuantumParallelRepetition.lean#L45210-L45320

import Definitions.Def_quantum_parallel_repetition_game
import Definitions.Def_qpr_core_23
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.Group.Submonoid.Defs
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Unbundled.Basic
import Mathlib.Algebra.Order.GroupWithZero.Unbundled.Basic
import Mathlib.Algebra.Order.GroupWithZero.Unbundled.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Lp.WithLp
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
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Nat.Init
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Real.Basic
import Mathlib.Data.SetLike.Basic
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Tactic.CancelDenoms.Core
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.Linarith.Preprocessing
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Positivity.Core
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common
import Mathlib.Topology.Defs.Filter

open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder

theorem
    QuantumParallelRepetition.exists_proofDSVDensityRationalHeterogeneousStoppedCommonStopGaugeErrorBound
    {d N B : ℕ} (grid : 0 < N) (dimension : 0 < d)
    (phases : 0 < B) {Q : ℕ} (fine : 0 < Q)
    (ε : ℝ) (precision : 0 < ε) :
    ∃ n : ℕ, 0 < n ∧
      ∃ A C : Fin B → Option ℕ →
          Matrix.unitaryGroup (Fin (N * n)) ℂ,
        ∀ {S L : ℕ}
          (width : Fin S → ℝ) (schedule : Fin L → Fin S)
          (ξ ζ : BipartiteUnitVector d),
          dSVDensityRationalHeterogeneousStoppedCommonStopGaugeError
              Q n width schedule ξ ζ A C ≤
            (10 + 8 * ((Q : ℝ) / (B : ℝ))) *
                dSVDensityRationalHeterogeneousPhysicalStoppedAsynchronousMass
                  N width schedule ξ ζ +
              (4 * ε ^ 2 +
                16 * (Real.exp (((B : ℝ) + 1) / (Q : ℝ)) - 1) +
                8 / (B : ℝ)) := by sorry
