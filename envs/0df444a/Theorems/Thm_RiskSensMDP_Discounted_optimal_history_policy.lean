-- Prove2me | Theorems.Thm_RiskSensMDP_Discounted_optimal_history_policy
-- name    : RiskSensMDP.Discounted.optimal_history_policy
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:28:37.37201+00:00
-- url     : https://prove2.me/theorems/f394aeca-a3a1-4019-823e-1b4e295c2de8
-- title:
--   Theorem 3.6(c) — optimal discounted finite-horizon history policy
-- statement:
--   In the bounded positive-cost model under (CC), for each $1\le k\le N$ there is an admissible measurable rule $f_k^*$ minimizing $V_{k-1}$. Take any family of such minimizers. At stage $n<N$, with history $h_n=(x_0,a_0,\ldots,x_n)$, set
--
--   $$g_n^*(h_n)=f_{N-n}^*\!\left(x_n,\sum_{j=0}^{n-1}\beta^j c(x_j,a_j),\beta^n\right).$$
--
--   These rules form a measurable admissible history-dependent policy. For every initial state $x$, it attains the value of problem (3.7) against all history policies:
--
--   $$E_x^{g^*}[U(C_\beta^N)]=J_N(x)=\inf_{\sigma\in\Pi}E_x^\sigma[U(C_\beta^N)].$$
--
--   This converts the stagewise Bellman minimizers into an optimal policy for the original finite-horizon cost problem. **Formalization Note** The empty sum at $n=0$ is zero, so the single formula includes the paper's displayed rule $g_0^*(x_0)=f_N^*(x_0,0,1)$.
-- source:
--   Bäuerle & Rieder, More Risk-Sensitive Markov Decision Processes, authors' manuscript (KIT repository 1000039663; published Math. Oper. Res. 39(1):105–120, 2014), p. 10, (3.7), p. 11, Theorem 3.6(c)

import Mathlib
import Definitions.Def_RiskSensMDP_Discounted_Model

open MeasureTheory ProbabilityTheory Filter

namespace RiskSensMDP.Discounted

/-- Theorem 3.6(c), authors' manuscript p. 11, relative to the objective (3.7),
p. 10. Each finite-horizon value has a minimizing extended-state rule. Every
family of such rules gives the displayed history policy, optimal among all
measurable history-dependent policies. Formalization Note: for stage zero the
discounted history sum is zero and `β⁰=1`, giving the paper's separate formula
`g₀*(x₀)=f_N*(x₀,0,1)`. -/
theorem optimal_history_policy {E A : Type*}
    [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    [TopologicalSpace.MetrizableSpace E] [SecondCountableTopology E]
    [StandardBorelSpace E]
    [TopologicalSpace A] [MeasurableSpace A] [BorelSpace A]
    [TopologicalSpace.MetrizableSpace A] [SecondCountableTopology A]
    [StandardBorelSpace A]
    (M : Model E A) (hBounds : HasBounds M) (hCC : HasCC M)
    (N : ℕ) :
    (∀ k ∈ Finset.Icc 1 N,
      ∃ f : DecisionRule M,
        IsMinimizer M (fun s => value M (k - 1) s.1 s.2.1 s.2.2) f) ∧
    (∀ fs : ℕ → DecisionRule M,
      (∀ k ∈ Finset.Icc 1 N,
        IsMinimizer M (fun s => value M (k - 1) s.1 s.2.1 s.2.2) (fs k)) →
      ∃ σ : Policy M.P,
        (∀ n < N, ∀ h : History E A, ValidHistory M.P n h →
          σ.g n h =
            (fs (N - n)).f
              (h.2, (discountedHistoryCost M h.1, M.β ^ n))) ∧
        (∀ x : E, policyValue M σ N x 0 1 = objective M N x)) := by sorry

end RiskSensMDP.Discounted
