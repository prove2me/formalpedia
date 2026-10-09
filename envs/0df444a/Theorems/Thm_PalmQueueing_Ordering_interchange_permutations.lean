-- Prove2me | Theorems.Thm_PalmQueueing_Ordering_interchange_permutations
-- name    : PalmQueueing.Ordering.interchange_permutations
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-02T02:39:58.187984+00:00
-- url     : https://prove2.me/theorems/9df599ff-daa6-403c-8fb6-f7862eaa96bf
-- title:
--   Lemma 4.1.3 — the interchange permutations
-- statement:
--   **Lemma 4.1.3.** Consider the $GI/GI$ single-server queue of §4.1.3, started empty (customer $0$
--   finds an empty queue), with input $A = \sum_{k\ge0}\delta_{T_k,\sigma_k}$, run under a
--   non-preemptive discipline $\phi$ that uses no information on the service times, and let $\psi$ be
--   FIFO. There exists a sequence of random permutations $\gamma_n : \mathbb{N} \to \mathbb{N}$,
--   $n \ge 0$, where $\gamma_n$ differs from identity on $\{0,1,\dots,n\}$ only, and such that for all
--   $n$, the counting measure $A^n = \sum_{k\ge0}\delta_{T_k,\sigma_{\gamma_n(k)}}$ satisfies:
--
--   * (a) $I_t(A,\phi) = I_t(A^n,\psi)$, for all $t \le T_n$;
--   * (b) $S_n(A,\phi) = S_n(A^n,\psi)$;
--   * (c) $A$ and $A^n$ are equivalent in distribution.
--
--   Here $I_t$ is the congestion process and $S_n$ the residual service state at the arrival epoch
--   $T_n$. (a) and (b) are pathwise identities, for every sample path; (c) is a statement about laws.
--
--   This is the **interchange argument**: the queue under $\phi$ is reproduced, up to $T_n$, by FIFO
--   fed with a reordered service sequence, and the reordering does not change the law of the input.
--   It holds because, conditionally on the information available to the discipline at $T_n$, the
--   required service times of the customers who have not yet started their service are i.i.d. with the
--   law of $\sigma_0$.
--
--   **Formalization Note.** The queue model (input, disciplines, observables) is the definition module
--   `PalmQueueing.Ordering.Disciplines`. The vector $S_n$ is compared through its discipline-free
--   content: the residual service time of the customer in service and the multiset of service times of
--   the waiting customers (the book lists the coordinates in a discipline-specific order).
-- source:
--   Baccelli & Bremaud, Elements of Queueing Theory: Palm Martingale Calculus and Stochastic Recurrences, 2nd ed., Springer 2003, p. 268, Lemma 4.1.3

import Mathlib
import Definitions.Def_PalmQueueing_Ordering_Disciplines

/-!
# Lemma 4.1.3: the interchange permutations (§4.1.3, p.268)
-/

namespace PalmQueueing.Ordering

open MeasureTheory

/-- **Lemma 4.1.3** (p.268). There exists a sequence of random permutations `γ_n : ℕ → ℕ`,
`n ≥ 0`, where `γ_n` differs from identity on `{0, 1, …, n}` only, and such that for all `n`, the
counting measure `A^n = Σ_{k≥0} δ_{T_k, σ_{γ_n(k)}}` satisfies:

(a) `I_t(A, φ) = I_t(A^n, ψ)` for all `t ≤ T_n`;
(b) `S_n(A, φ) = S_n(A^n, ψ)`;
(c) `A` and `A^n` are equivalent in distribution.

Here `A` is the `GI/GI` input of the queue (p.267), `φ` is any non-preemptive discipline using
no information on the service times (the class of §4.1.3, p.266), and `ψ` is FIFO. The queue
starts empty: customer `0` finds an empty queue.

(a) and (b) are pathwise identities; (b) compares the residual service time of the customer in
service and the multiset of service times of the waiting customers at `T_n` (`residualState`),
which is the content of the vector `S_n` independent of the order in which each discipline lists
its coordinates. (c) is where the hypotheses on `φ` and on the input are spent. -/
theorem interchange_permutations {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (A : GIGIInput Ω P) (φ : Discipline) :
    ∃ gam : ℕ → Ω → ℕ → ℕ,
      (∀ (n : ℕ) (ω : Ω), PermFixedBeyond (gam n ω) n) ∧
      (∀ (n : ℕ) (ω : Ω) (t : ℝ), t ≤ A.T n ω →
        congestion φ Set.univ (fun k => A.T k ω) (fun k => A.sigma k ω) (fun k => A.U k ω) t =
          congestion fifo Set.univ (fun k => A.T k ω) (fun k => A.sigma (gam n ω k) ω)
            (fun k => A.U k ω) t) ∧
      (∀ (n : ℕ) (ω : Ω),
        residualState φ Set.univ (fun k => A.T k ω) (fun k => A.sigma k ω) (fun k => A.U k ω) n =
          residualState fifo Set.univ (fun k => A.T k ω) (fun k => A.sigma (gam n ω k) ω)
            (fun k => A.U k ω) n) ∧
      (∀ n : ℕ, SameInputLaw P A.T A.sigma (gam n)) := by sorry

end PalmQueueing.Ordering
