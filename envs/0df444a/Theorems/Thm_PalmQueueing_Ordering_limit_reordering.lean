-- Prove2me | Theorems.Thm_PalmQueueing_Ordering_limit_reordering
-- name    : PalmQueueing.Ordering.limit_reordering
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-02T02:49:54.152758+00:00
-- url     : https://prove2.me/theorems/badbb832-79da-41fa-9013-0557dbf7b266
-- title:
--   Lemma 4.1.4 — the limit reordering
-- statement:
--   **Lemma 4.1.4.** In the setting of Lemma 4.1.3, let $\gamma_n(m)$ be the customer served $m$-th under
--   $\phi$ when the queue is fed by $A_{[0,n]}$ ($m \le n$; the identity beyond $n$), and assume the
--   traffic intensity $\rho = E[\sigma_0]/E[T_1 - T_0]$ satisfies $\rho < 1$. Then almost surely, for
--   every $k$, $\gamma_n(k)$ does not depend on $n$ after a finite rank; let $\gamma = \lim_n\gamma_n$
--   and define $A'$ by
--   $$ A'(C \times K) = \lim_{n\to\infty} A^n(C \times K), \tag{4.1.19} $$
--   that is, $A' = \sum_{k\ge0}\delta_{T_k,\sigma_{\gamma(k)}}$. The point process $A'$ is equivalent
--   in law to $A$, and almost surely, for all $n \ge 0$,
--   $$ B_{\gamma(n)}(A,\phi) = B_n(A',\psi), \qquad D_{\gamma(n)}(A,\phi) = D_n(A',\psi) , \tag{4.1.20} $$
--   where $B_n$ and $D_n$ are the times at which customer $n$ begins and leaves his service.
--
--   The stability of $\gamma_n$ is the book's own justification for (4.1.19) ("$\gamma_n$ only permutes
--   indices within a busy period") and is stated as the first conclusion. (4.1.20) is what the FIFO
--   optimality proof consumes: the beginning and departure times of the two systems coincide up to the
--   relabelling $\gamma$, so the waiting time vectors are reorderings of each other, and Lemma 4.1.2
--   gives $V(A',\psi) \prec V(A,\phi)$.
--
--   **Formalization Note.** $\rho < 1$ is stated as $E[\sigma_0] < E[T_1 - T_0]$ with both
--   integrable. The page calls $\gamma(k)$ a rank; (4.1.20) needs $\gamma$ to map a rank to the
--   customer of that rank, and that is the reading used.
-- source:
--   Baccelli & Bremaud, Elements of Queueing Theory: Palm Martingale Calculus and Stochastic Recurrences, 2nd ed., Springer 2003, p. 270, Lemma 4.1.4

import Mathlib
import Definitions.Def_PalmQueueing_Ordering_Disciplines

/-!
# Lemma 4.1.4: the limit reordering (§4.1.3, p.270)
-/

namespace PalmQueueing.Ordering

open MeasureTheory

/-- **Lemma 4.1.4** (p.270). The point process `A'` is equivalent in law to `A`, and such that for
all `n ≥ 0`,

`(4.1.20)  B_{γ(n)}(A, φ) = B_n(A', ψ),   D_{γ(n)}(A, φ) = D_n(A', ψ)`.

`A'` is defined by `A'(C × K) = lim_n A^n(C × K)` (4.1.19), with `γ_n` the permutations of the
proof of Lemma 4.1.3 (`rankPerm`: `γ_n(m)` is the customer served `m`-th under `φ` when the queue
is fed by `A_{[0,n]}`). "If `ρ < 1`, this a.s. limit is well defined since the permutations `γ_n`
are then such that `γ_n(k)` does not depend on `n` after a finite rank"; that claim is the first
conclusion, and `γ = lim_n γ_n` is `limitPerm`, so that `A' = Σ_k δ_{T_k, σ_{γ(k)}}`.

`ρ = E[σ_0] / E[τ_0] < 1`, with `τ_0 = T_1 − T_0`, is stated as `E[σ_0] < E[τ_0]` with both
integrable. -/
theorem limit_reordering {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (A : GIGIInput Ω P) (φ : Discipline)
    (hσint : Integrable (A.sigma 0) P) (hτint : Integrable (fun ω => A.T 1 ω - A.T 0 ω) P)
    (hρ : ∫ ω, A.sigma 0 ω ∂P < ∫ ω, (A.T 1 ω - A.T 0 ω) ∂P) :
    (∀ᵐ ω ∂P, ∀ k : ℕ, ∃ N : ℕ, ∀ n ≥ N,
      rankPerm φ (fun k => A.T k ω) (fun k => A.sigma k ω) (fun k => A.U k ω) n k =
        rankPerm φ (fun k => A.T k ω) (fun k => A.sigma k ω) (fun k => A.U k ω) N k) ∧
    SameInputLaw P A.T A.sigma
      (fun ω => limitPerm φ (fun k => A.T k ω) (fun k => A.sigma k ω) (fun k => A.U k ω)) ∧
    (∀ᵐ ω ∂P, ∀ n : ℕ,
      beginTime φ Set.univ (fun k => A.T k ω) (fun k => A.sigma k ω) (fun k => A.U k ω)
          (limitPerm φ (fun k => A.T k ω) (fun k => A.sigma k ω) (fun k => A.U k ω) n) =
        beginTime fifo Set.univ (fun k => A.T k ω)
          (fun k => A.sigma
            (limitPerm φ (fun k => A.T k ω) (fun k => A.sigma k ω) (fun k => A.U k ω) k) ω)
          (fun k => A.U k ω) n ∧
      departTime φ Set.univ (fun k => A.T k ω) (fun k => A.sigma k ω) (fun k => A.U k ω)
          (limitPerm φ (fun k => A.T k ω) (fun k => A.sigma k ω) (fun k => A.U k ω) n) =
        departTime fifo Set.univ (fun k => A.T k ω)
          (fun k => A.sigma
            (limitPerm φ (fun k => A.T k ω) (fun k => A.sigma k ω) (fun k => A.U k ω) k) ω)
          (fun k => A.U k ω) n) := by sorry

end PalmQueueing.Ordering
