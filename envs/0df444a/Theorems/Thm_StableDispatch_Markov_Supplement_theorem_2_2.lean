-- Prove2me | Theorems.Thm_StableDispatch_Markov_Supplement_theorem_2_2
-- name    : StableDispatch.Markov.Supplement.theorem_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T09:46:57.634846+00:00
-- url     : https://prove2.me/theorems/d19172cb-bfd5-4689-a94d-268334cad88a
-- title:
--   Theorem 2.2, p. 12 — instability of weakly symmetric policies with o(log n) memory and o(n²) message rate
-- statement:
--   **Setting.** There are $n$ servers with rates $\mu\in\Sigma_n=\{\mu\in(0,\infty)^n:\sum_i\mu_i=n\}$, each with an infinite FIFO queue. Jobs arrive as a renewal process of rate $\lambda n$ (interarrival law $F_n$ on $[0,\infty)$ with mean $1/(\lambda n)$), with i.i.d. sizes of law $\nu$ on $[0,\infty)$ with mean one. A **memory-based dispatching policy** (§2.3) has memory states $\mathcal M_n$, a spontaneous-message rate $\beta_n$ and measurable maps $f_1,f_2,f_3,g_1,g_2,g_3,h_1,h_2$ that decide whom to sample, where to send each job and how to update the memory at arrivals, at spontaneous messages and at departures. The process $(\mathbf Q(\cdot),M(\cdot),Z(\cdot))$ of workload sequences, memory state and time since the last arrival is constructed from the fundamental processes as in §2.3.2. A policy is **weakly symmetric** if it satisfies Assumption 2.1; its **average message rate** is (2.2); its **stability region** $\Gamma_n(\lambda)$ is the set of $\mu\in\Sigma_n$ for which $(\mathbf Q,M,Z)$ is positive Harris recurrent.
--
--   **Theorem 2.2 (instability of resource-constrained policies).** Let $\lambda\in(0,1)$ and let $(\alpha_n)_{n\ge1}$ be positive. There are sets $\Gamma_n(\lambda,\alpha_n)$ with
--
--   $$\Gamma_n(\lambda,\alpha_n)\subsetneq\Sigma_n\qquad(n\ge1)$$
--
--   such that, if $\alpha_n\in o(n^2)$, then for all interarrival laws $F_n$ and every job-size law $\nu$ as above, every $c_n\in o(\log n)$ and every sequence of weakly symmetric policies with at most $c_n$ bits of memory ($|\mathcal M_n|\le 2^{c_n}$) whose average message rate is at most $\alpha_n$ almost surely, there is $N$ with
--
--   $$\Gamma_n(\lambda)\subseteq\Gamma_n(\lambda,\alpha_n)\qquad\text{for all } n\ge N.$$
--
--   So no weakly symmetric policy with $o(\log n)$ memory and $o(n^2)$ messages per unit time is stable for every rate vector: for all large $n$ some $\mu\in\Sigma_n$, not depending on the policy, makes it unstable. The single-ID policy of Theorem 2.1, which is stable on all of $\Sigma_n$, uses $\log_2 n$ bits of memory, and the theorem shows that this order of memory cannot be reduced.
--
--   **Formalization Note** The construction is event driven: at simultaneous events, departures (in increasing server index) come before arrivals, which come before spontaneous-message events; a job of size $0$ departs at its arrival instant. $U_{7,k},U_{8,k}$ are used at the $k$-th departure of each server. The delay of the arrival process is the residual interarrival time given the initial age $Z(0)$. Positive Harris recurrence is the occupation-time form with an invariant probability, on the states with finitely many jobs in each queue and an attainable age; on all of $\mathbb R_+^{\mathbb Z_+}$ no process would be recurrent and the theorem would hold vacuously. The message-rate bound is required for every $\mu\in\Sigma_n$ and every initial state.
--
--   Differences from the source:
--
--   - reading: Γ_n(λ, α_n), which by Remark 2.5 (p. 12) only depends on n, the arrival rate λ and α_n; one renewal arrival process of rate λn and one job-size distribution with unit mean as model primitives → ∃ Γ is chosen before the interarrival laws F_n (any law on [0, ∞) with mean 1/(λn), for each n) and the single job-size law ν (any law on [0, ∞) with mean one), which are quantified after it, so Γ depends only on λ and (α_n); N may depend on the laws; reason: Remark 2.5 states this dependence; the proof's set (pp. 20–23) uses ε_n < b_n = (λp_{1/2}/6)3^{−α_n/(λnp_{1/2})}, and since p_{1/2} = P(W_1 ≥ 1/2) > 0 for every unit-mean law and N may depend on the law, a law-free choice such as ε_n = (λ/(12n))3^{−α_n} lies below b_n for all large n; the arrival process enters the proof only through its rate λn
--   - generalization: M_n = {1, …, 2^{c_n}} → 1 ≤ memSize ≤ 2^{c_n} memory states, c_n real; reason: the theorem says 'at most c_n bits'; memSize = 2^{c_n} is the paper's case
--   - reading: the arrival process is a 'delayed renewal process' with independent initial condition Z(0) → under the initial state x with age z, the first arrival comes after τ − z with τ ~ F_n conditioned on τ > z, and later interarrival times are i.i.d. F_n; reason: this is the delay that makes (Q, M, Z) the Markov process §2.3.2 says it constructs; with any other delay no invariant probability exists in general for non-Poisson arrivals and the stability region would be empty
--   - reading: 'positive Harris recurrent', not defined in the paper → the standard continuous-time definition (Meyn–Tweedie): a nonzero σ-finite φ such that φ(A) > 0 implies infinite occupation time of A a.s. from every state, plus an invariant probability measure; asked on the states whose queues hold finitely many jobs and whose age z ≥ 0 has F_n((z, ∞)) > 0; reason: on the full ℝ₊^{ℤ₊} a state with infinitely many jobs never empties, no policy would be recurrent and the theorem would be vacuous; §2.3 notes that queues with finitely many jobs are the relevant states
--   - reading: 'an average message rate (2.2) upper bounded by α_n almost surely' → for every µ ∈ Σ_n and every initial state of the state space, the lim sup (2.2), computed in [0, ∞], is ≤ α_n almost surely; reason: the bound is a property of the policy and is used in the proof (p. 21) for the rate vector with slow servers
--   - reading: 'αn ∈ o(n²)' in the property → α =o[atTop] n² is a hypothesis of the property, after ∃ Γ; reason: Γ_n ⊊ Σ_n holds for every positive (α_n); placing the hypothesis inside or outside is equivalent because a proper subset of the nonempty Σ_n always exists
--   - encoding: event times, simultaneous events and zero-size jobs are left implicit; U_{7,k}, U_{8,k} at the k-th departure T^d_k(i) → departures (in increasing server index) precede arrivals, which precede spontaneous-message events, at equal times; a job of size 0 departs at its arrival instant (this departure may trigger an h_1 message); U_{7,k}, U_{8,k} are used at the k-th departure of each server i; if events accumulate before t (a null event) the path is set to its initial state; reason: the paper does not fix these conventions; none of them changes the policy class or the hypotheses of the theorem
--   - encoding: maps on M_n × ℝ₊ × B_n × [0, 1] etc.; g_1 ∈ {0, 1, …, n}; h_1 ∈ {0, 1}; servers {1, …, n}; B_n a set of triples → real arguments, measurable on each fiber of the discrete arguments; g_1 : Option (Fin n) (none = no message); h_1 : Bool; Fin n; B_n as partial maps i ↦ (q_i, µ_i); policies exist only for n ≥ 1, so sequences are indexed by n ≥ 1; reason: Lean conventions; values off the paper's domains never enter the dynamics
--   - encoding: a Poisson process of rate β_n → β_n > 0; reason: an exponential law needs a positive rate; a rate-0 process is the same as g_1 ≡ none
-- source:
--   Gamarnik, Tsitsiklis, Zubeldia, Stability, Memory, and Messaging Trade-Offs in Heterogeneous Service Systems, arXiv:2007.07219v1, p. 12, Theorem 2.2; proof Appendix B, pp. 18–23

import Mathlib
import Definitions.Def_MatrixAnalytic_Tree_Process
import Definitions.Def_StableDispatch_Markov_Setting
import Definitions.Def_StableDispatch_Markov_Supplement_Harris
import Definitions.Def_StableDispatch_Markov_Supplement_Policy
import Definitions.Def_StableDispatch_Markov_Supplement_Dynamics

namespace StableDispatch.Markov.Supplement

open MeasureTheory Asymptotics Filter

theorem theorem_2_2 (lam : ℝ) (hlam0 : 0 < lam) (hlam1 : lam < 1)
    (α : ℕ → ℝ) (hα : ∀ n, 0 < α n) :
    ∃ Γ : (n : ℕ) → Set (Fin n → ℝ),
      (∀ n, 1 ≤ n → Γ n ⊂ StableDispatch.Markov.Sigma n) ∧
      (α =o[atTop] (fun n : ℕ => (n : ℝ) ^ 2) →
        ∀ F : ℕ → Measure ℝ, (∀ n, 1 ≤ n → IsInterarrivalLaw lam n (F n)) →
        ∀ ν : Measure ℝ, IsJobSizeLaw ν →
        ∀ c : ℕ → ℝ, c =o[atTop] (fun n : ℕ => Real.log n) →
        ∀ P : ∀ n : ℕ, 1 ≤ n → Policy n,
          (∀ n (hn : 1 ≤ n), WeaklySymmetric (P n hn)) →
          (∀ n (hn : 1 ≤ n), ((P n hn).memSize : ℝ) ≤ (2 : ℝ) ^ c n) →
          (∀ n (hn : 1 ≤ n), MessageRateBounded (P n hn) (F n) ν (α n)) →
          ∃ N : ℕ, ∀ n (hn : 1 ≤ n), N ≤ n →
            stabilityRegion (P n hn) (F n) ν ⊆ Γ n) := by sorry

end StableDispatch.Markov.Supplement
