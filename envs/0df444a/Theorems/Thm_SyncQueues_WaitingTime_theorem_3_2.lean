-- Prove2me | Theorems.Thm_SyncQueues_WaitingTime_theorem_3_2
-- name    : SyncQueues.WaitingTime.theorem_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:13:48.836209+00:00
-- url     : https://prove2.me/theorems/2adc0a56-ba9d-45ec-8c51-b2db9a5c66a4
-- title:
--   Theorem 3.2, p. 13 (fixed job size) — stability, and convergence with all moments of the stationary waiting time to the endogenous solution of the high-order Lindley equation
-- statement:
--   This is the paper's main theorem, for jobs of a fixed size $m$.
--
--   Consider, for each number of servers $n\ge m$, the synchronized FCFS network of the definitions file: Poisson arrivals at rate $\lambda n$, every job split into $m$ pieces routed to $m$ distinct uniformly chosen servers, with joint service law $B_m$ on $[0,\infty)^m$. Each $n$-system lives on its own probability space. Let $W^{(n,t_0)}_\emptyset$ be the waiting time, excluding service, of the tagged job (the first job to arrive after time zero) when the system starts empty at time $t_0<0$. Let $B$ be the law of a randomly chosen piece and $\lambda^*=\lambda m$. Suppose that for some $\beta>0$, $E[e^{\beta\chi}]<\infty$ and
--   $$m\,E\big[e^{\beta\chi}\big]\,\frac{\lambda m}{\lambda m+\beta}<1,\qquad\chi\sim B.\tag{3.5}$$
--   Then there are random variables $W^{(n)}$ such that:
--
--   1. for every $n\ge m$, $\lim_{t_0\to-\infty}W^{(n,t_0)}_\emptyset=W^{(n)}$ almost surely, with $W^{(n)}$ finite;
--   2. the endogenous solution of (3.3) on the $m$-ary weighted branching tree,
--   $$W=\bigvee_{r=0}^\infty\ \bigvee_{\mathbf j\in A_r}S_{\mathbf j},\qquad S_{\mathbf j}=\sum_{t=1}^{|\mathbf j|}(\chi_{\mathbf j|t}-\tau_{\mathbf j|t}),$$
--   with i.i.d. marks $\chi\sim B$, $\tau\sim\mathrm{Exp}(\lambda^*)$, is almost surely finite;
--   3. $W^{(n)}\Rightarrow W$ as $n\to\infty$;
--   4. for every $p>0$, $E[W^p]<\infty$, $E[(W^{(n)})^p]<\infty$ for all large $n$, and
--   $$E\big[(W^{(n)})^p\big]\longrightarrow E\big[W^p\big],\qquad n\to\infty .$$
--
--   The theorem gives both the stability of the network for each $n$ and an explicit description of its stationary waiting time for many servers; for $m=1$, $W$ is the supremum of a random walk, the Lindley representation of the M/G/1 waiting time.
--
--   **Formalization Note** The statement is the case of jobs of fixed size $m$ ($f_n=f=\delta_m$). For random job sizes the limit printed in the source is not correct, because the immediate predecessors of a job are size-biased (a job of size $k$ is a predecessor with probability proportional to $k$). A simulation with $n=1000$ servers and U(0,1) pieces gives: sizes $\{1,3\}$ w.p. $1/2$, $\lambda=0.1$: simulated $E W=0.0952$, the printed (3.3) gives $0.0848$, the size-biased fixed point $0.0958$; sizes $\{1,5\}$ w.p. $0.7/0.3$, $\lambda=0.05$: $0.0546$, $0.0450$, $0.0541$; fixed $m=2$, $\lambda=0.1$: $0.0870$, $0.0878$, $0.0873$. For fixed size the size-biased law is $\delta_m$ again, and the printed statement is correct. Under this restriction Assumption 3.1 (i) and (iii) hold automatically and (ii) coincides with (3.5), since $\lambda^*_n=\lambda m$ for every $n$. Added to the page: the integrability $E[e^{\beta\chi}]<\infty$ next to (3.5) (implicit on the page; without it the Bochner integral is $0$); the systems exist only for $n\ge m$; $B$ is the average of the coordinate marginals of $B_m$; a.s. finiteness of $W$ and integrability of the moments are stated so that the real supremum and the Bochner integrals are the true ones. Moments use the real power $x^p$ of nonnegative quantities, so every $p>0$ is covered. The random variables $W^{(n)}$ are existential but pinned down almost surely by the limit in 1.
-- source:
--   Olvera-Cravioto & Ruiz-Lacedelli, arXiv:1501.00186v3, p. 13, Theorem 3.2 (with (3.3), p. 11; (3.4) and Assumption 3.1, p. 12; (3.9), p. 15), restricted to $f_n=f=\delta_m$; proofs pp. 21–23 and 23–33

import Mathlib
import Definitions.Def_SyncQueues_WaitingTime_BranchingTree
import Definitions.Def_SyncQueues_WaitingTime_Model

namespace SyncQueues.WaitingTime

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

theorem theorem_3_2 {m : ℕ} (hm : 0 < m) {lam : ℝ} (hlam : 0 < lam)
    (Bm : Measure (Fin m → ℝ)) [IsProbabilityMeasure Bm] (hBm : ∀ᵐ x ∂Bm, ∀ i, 0 ≤ x i)
    {β : ℝ} (hβ : 0 < β)
    (hint : Integrable (fun x => Real.exp (β * x)) (pieceLaw Bm))
    (hstab : (m : ℝ) * (∫ x, Real.exp (β * x) ∂(pieceLaw Bm)) * (lam * m / (lam * m + β)) < 1)
    (Ω : ℕ → Type*) [∀ n, MeasurableSpace (Ω n)] (P : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (P n)]
    (E : ∀ n, ℕ → Ω n → ℝ) (R : ∀ n, ℕ → Ω n → (Fin m → ℕ)) (C : ∀ n, ℕ → Ω n → (Fin m → ℝ))
    (hsys : ∀ n, m ≤ n → IsSyncSystem (P n) m n lam Bm (E n) (R n) (C n))
    {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (χ τ : List (Fin m) → Ω' → ℝ) (htree : IsLimitTree P' (pieceLaw Bm) (lam * m) χ τ) :
    ∃ W : ∀ n, Ω n → ℝ,
      (∀ n, m ≤ n → ∀ᵐ ω ∂(P n),
        Tendsto (fun t0 => waitT (fun k => E n k ω) (fun k => R n k ω) (fun k => C n k ω) t0) atBot (𝓝 (W n ω))) ∧
      (∀ᵐ ω ∂P', BddAbove (Set.range fun j => pathSum χ τ j ω)) ∧
      TendstoInDistribution W atTop (endoW χ τ) P P' ∧
      ∀ p : ℝ, 0 < p →
        Integrable (fun ω => endoW χ τ ω ^ p) P' ∧
        (∀ᶠ n in atTop, Integrable (fun ω => W n ω ^ p) (P n)) ∧
        Tendsto (fun n => ∫ ω, W n ω ^ p ∂(P n)) atTop
          (𝓝 (∫ ω, endoW χ τ ω ^ p ∂P')) := by sorry

end SyncQueues.WaitingTime
