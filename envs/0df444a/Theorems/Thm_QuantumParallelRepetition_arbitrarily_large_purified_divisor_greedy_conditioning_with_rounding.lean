-- Prove2me | Theorems.Thm_QuantumParallelRepetition_arbitrarily_large_purified_divisor_greedy_conditioning_with_rounding
-- name    : QuantumParallelRepetition.arbitrarily_large_purified_divisor_greedy_conditioning_with_rounding
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-11T07:47:46.606896+00:00
-- url     : https://prove2.me/theorems/a2fd8ca9-02cc-4f9c-b499-853023f6d68b
-- title:
--   Arbitrarily long repetitions admit a greedily conditioned purified strategy with a fixed rounding divisor
-- statement:
--   Let $G$ be a finite two-player one-round game and suppose the sequence $n\mapsto\omega^*(G^n)$ has a subexponential witness, i.e. for all $c,C>0$ there is an $n$ with $\omega^*(G^n)>C e^{-cn}$. Fix $0<\eta\le 1$, $K\ge 0$ and $\delta>0$. Then there is an integer $q\ge 2$, chosen once and for all, such that for every threshold $N_0$ one can find some $n>N_0$, a strategy $S$ for $G^n$, and a set of coordinates $D\subseteq\{1,\dots,n\}$ with the following five properties, where $\tilde S$ denotes the purification of $S$ and $p_D$ is the probability that $\tilde S$ wins every coordinate of $D$ simultaneously: the winning probability of $\tilde S$ exceeds $e^{-\eta n/(4q)}$; $|D|<\lfloor n/q\rfloor$; the winning probability of $\tilde S$ is at most $p_D$; the total conditional failure mass of the coordinates outside $D$ is strictly less than $(n-|D|)\,\eta\,p_D$, so on average a remaining coordinate fails with conditional probability below $\eta$; and the per-coordinate information cost is already rounded down to budget, $$\frac{8K\,\log\!\big(\Lambda(D)/p_D\big)}{n-|D|}\ \le\ \delta^{2},\qquad \Lambda(D)=\big(|A|\,|B|\big)^{|D|}.$$
-- source:
--   OpenAI, ten-proofs, QuantumParallelRepetition.lean, https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/QuantumParallelRepetition.lean#L41251-L41329

import Definitions.Def_quantum_parallel_repetition_game
import Definitions.Def_qpr_core_22
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.GroupWithZero.Unbundled.Basic
import Mathlib.Algebra.Order.GroupWithZero.Unbundled.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.SDiff
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Nat.Init
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Order.Basic
import Mathlib.Order.Defs.PartialOrder
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
open scoped BigOperators InnerProductSpace
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem QuantumParallelRepetition.arbitrarily_large_purified_divisor_greedy_conditioning_with_rounding
    (G : Game X Y A B)
    (hwitness : HasSubexponentialWitness (repeatedEntangledValue G))
    {η K δ : ℝ}
    (hη : 0 < η) (hη_one : η ≤ 1)
    (hK : 0 ≤ K) (hδ : 0 < δ) :
    ∃ q : ℕ, 2 ≤ q ∧
      ∀ N₀ : ℕ, ∃ n : ℕ, N₀ < n ∧
        ∃ S : Strategy (G.repeat n),
          ∃ D : Finset (Fin n),
            Real.exp (-(η / (4 * (q : ℝ))) * (n : ℝ)) <
              (purifiedStrategy S).winProbability ∧
            D.card < n / q ∧
            (purifiedStrategy S).winProbability ≤
              (strategyEventLaw (G.repeat n) (purifiedStrategy S)).eventMass
                (FiniteEventLaw.winEvent
                  (repeatedCoordinateWin G n) D) ∧
            (∑ i ∈ Finset.univ \ D,
              FiniteEventLaw.failureMass
                (strategyEventLaw (G.repeat n) (purifiedStrategy S))
                (repeatedCoordinateWin G n) D i) <
              ((Finset.univ \ D).card : ℝ) *
                (η *
                  (strategyEventLaw (G.repeat n)
                    (purifiedStrategy S)).eventMass
                      (FiniteEventLaw.winEvent
                        (repeatedCoordinateWin G n) D)) ∧
            8 * K *
                Real.log
                  (fullHistoryAnswerCount (A := A) (B := B) D /
                    (strategyEventLaw (G.repeat n)
                      (purifiedStrategy S)).eventMass
                        (FiniteEventLaw.winEvent
                          (repeatedCoordinateWin G n) D)) /
                  ((Finset.univ \ D).card : ℝ) ≤
              δ ^ 2 := by sorry
