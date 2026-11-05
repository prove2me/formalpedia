-- Prove2me | Theorems.Thm_RiskSensMDP_AverageCost_stationary_state_process
-- name    : RiskSensMDP.AverageCost.stationary_state_process
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-11-05T02:15:20.000658+00:00
-- url     : https://prove2.me/theorems/73624c0b-2915-457d-9bdb-cc73da5ce8fd
-- title:
--   Under a stationary policy (f,f,…) the actions are f(X_n) and the state process is the Markov chain with kernel Q(·|x,f(x))
-- statement:
--   Let $(E,A,D,Q,c)$ be the Borel MDP of Bäuerle & Rieder (§2) and let $\pi=(f,f,\dots)$ be a stationary policy given by a measurable decision rule $f$ with $f(x)\in D(x)$. Let $P^\pi_x$ be the law of the controlled trajectory $((X_0,A_0),(X_1,A_1),\dots)$ started at $X_0=x$. Then
--
--   1. the actions are $A_n=f(X_n)$ for all $n$, $P^\pi_x$-almost surely;
--   2. the law of the state process $(X_n)_{n\ge0}$ under $P^\pi_x$ is the law of the time-homogeneous Markov chain with transition kernel
--   $$
--   P_f(x,B)=Q(B\mid x,f(x))
--   $$
--   started at $x$.
--
--   This is the identification, used implicitly on p. 17 of the paper ("the corresponding controlled Markov chain $(X_n)$"), that lets Markov-chain results such as the Harris law of large numbers be applied to the cost process of a stationary policy.
--
--   **Formalization Note** $P^\pi_x$ is `pathMeasure M f.toPolicy x` and the chain law is `chainLaw (stateKernel M f) x`; item 2 says that the pushforward of $P^\pi_x$ under $\omega\mapsto(\omega_n.1)_n$ equals the chain law.
-- source:
--   Bäuerle & Rieder, More Risk-Sensitive Markov Decision Processes, authors' manuscript (KIT repository 1000039663; Math. Oper. Res. 39(1):105–120, 2014), §2 p. 3 (construction of P^σ_x) and §5.1 p. 17 (Theorem 5.1: 'the corresponding controlled Markov chain (X_n)')

import Mathlib
import Definitions.Def_RiskSensMDP_AverageCost_Model
import Definitions.Def_RiskSensMDP_AverageCost_HarrisRecurrence

open MeasureTheory ProbabilityTheory Filter Finset

namespace RiskSensMDP.AverageCost

/-- Under a stationary policy the actions are `A_n = f(X_n)` a.s., and the state process is the
Markov chain with kernel `P_f(x, ·) = Q(· | x, f(x))` started at `x`. -/
theorem stationary_state_process {E A : Type*} [MeasurableSpace E] [StandardBorelSpace E]
    [MeasurableSpace A] [StandardBorelSpace A]
    (M : Model E A) (f : StationaryRule M) (x : E) :
    (∀ᵐ ω ∂(pathMeasure M f.toPolicy x), ∀ n : ℕ, (ω n).2 = f.f (ω n).1) ∧
    (pathMeasure M f.toPolicy x).map (fun ω n => (ω n).1) = chainLaw (stateKernel M f) x := by sorry

end RiskSensMDP.AverageCost
