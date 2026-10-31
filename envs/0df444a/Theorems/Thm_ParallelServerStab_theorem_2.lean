-- Prove2me | Theorems.Thm_ParallelServerStab_theorem_2
-- name    : ParallelServerStab.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:24:22.693744+00:00
-- url     : https://prove2.me/theorems/e3c35d2f-f75a-40e6-b900-65298850d8e7
-- title:
--   Theorem 2 — under non-idling J2SQ$(p)$, stability forces $\rho<V_{cr}(p)\wedge1$
-- statement:
--   Consider $s\ge2$ identical exponential servers with Poisson arrivals, traffic intensity $\rho=\lambda/(s\mu)$, under the non-idling policy J2SQ$^{NI}(p)$ for an error probability $p\in[0,1]$: an arriving job that finds an idle server joins one; otherwise it joins the shortest queue with probability $1-p$ and the second-shortest queue with probability $p$ (allocation vector $\mathbf p_{p,2}$). Then
--
--   $$
--   S^{NI}(\mathbf p_{p,2})\subseteq[0,\,V_{cr}(p)\wedge1),
--   $$
--
--   that is: for all $\lambda,\mu>0$ with $\rho<1$, if the system is stable and $p>0$, then $\rho<V_{cr}(p)$, where
--
--   $$
--   V_{cr}(p)=\frac{s-1}{2s}\left(1+\sqrt{1+\frac{4}{p(s-1)}}\right).
--   $$
--
--   The boundary $\rho=V_{cr}(p)$ is excluded. Since $V_{cr}(p)<1$ exactly when $p>1-1/s$ (eq. (10)), the traffic condition $\rho<1$ does not guarantee stability once routing errors are frequent enough, although the policy never leaves a server idle while a job waits.
--
--   **Formalization Note** Stability is positive recurrence of the empty state of the ordered queue process (`StableNI`).
--
--   Differences from the source:
--   - reading: $\subset$ → $\subseteq$; reason: strict inclusion would be false for $p \le 1-1/s$, where $V_{cr}(p)\wedge 1 = 1$ and $S^{NI}(p_{p,2})=[0,1)$ (Corollary 3); the paper uses $\subset$ for inclusion
--   - reading: $Q$ is a positive recurrent CTMC (§3.1, p. 8) → the empty state of the ordered chain is recurrent and its mean return time (holding times included) is finite; reason: the ordered chain is not irreducible on $\mathcal R(\mathbb Z_+^s)$ (under J2SQ$^{NI}$ the shortest queue never exceeds $1$ from the empty state), so positive recurrence of every state is false for every $\rho$; the paper argues from the empty state (Corollary 1)
--   - reading: $V_{cr}(p)$ for $p\in[0,1]$, with (9) defined for $p>0$ only → the conclusion $\rho<V_{cr}(p)$ is guarded by $0<p$; reason: the paper's $V_{cr}(0)=+\infty$ (the limit $p\to0^+$) makes the $p=0$ case the hypothesis $\rho<1$; Lean's $V_{cr}(0)$ would be the junk value $(s-1)/s$, and $p=0$ is JSQ, which is maximal
--   - reading: $s \ge 1$ servers in (9), $s$ servers in §3 → $s \ge 2$; reason: the model has $s \ge 2$ servers (§1, p. 1), $p_{p,2}=(1-p,p,0,\dots,0)$ needs two coordinates, and (9) divides by $p(s-1)$
--   - encoding: $\rho \in S^{NI}(\mathbf p)$, a set of traffic intensities in $[0,1)$ → for all $\lambda,\mu>0$ with $\rho=\lambda/(s\mu)<1$, stability of the chain with these rates; reason: stability depends on $\lambda,\mu$ only through $\rho$; $\rho=0$ ($\lambda=0$) is left out, where the conclusion holds outright
--   - encoding: ordered queue vectors in $\mathcal R(\mathbb Z_+^s)$, ranks $1,\dots,s$, uniform labels inside tie blocks → monotone `Fin s → ℕ`, 0-based ranks; routing to rank $i$ adds the job at the last rank of $i$'s tie block, a departure from rank $i$ removes it at the first rank of the block; an arrival that finds idle servers joins one chosen uniformly; reason: after re-sorting every choice inside a tie block gives the same ordered state, so these are the paper's transitions
--   - encoding: the CTMC $Q$ → its jump chain `jumpNI` and exit rates `rateNI` $=\lambda+\mu\cdot\#\{\text{busy servers}\}$; reason: a CTMC with no self-loops is determined by its jump chain and exit rates
-- source:
--   Moyal–Perry, Stability of Parallel Server Systems, arXiv:1904.10331v1, Theorem 2, p.11 (with S^NI from §3.1, p.8, and (9), p.11)

import Mathlib
import Definitions.Def_ParallelServerStab_Vcr
import Definitions.Def_ParallelServerStab_StableNI

namespace ParallelServerStab

/-- Theorem 2 (Moyal–Perry, Stability of Parallel Server Systems, arXiv:1904.10331v1,
Theorem 2, p. 11): `S^NI(p_{p,2}) ⊆ [0, V_cr(p) ∧ 1)` for every `p ∈ [0, 1]`. For `s ≥ 2`
servers, an error probability `p ∈ [0, 1]` and rates `λ, µ > 0` with `ρ = λ/(sµ) < 1`: if the
system under the non-idling J2SQ(p) policy (an arrival that finds an idle server joins one;
otherwise it joins the shortest queue with probability `1 − p` and the second-shortest with
probability `p`) is stable, then `ρ < V_cr(p)` whenever `p > 0`.

**Formalization Note.** Stability (`StableNI`) is positive recurrence of the empty state of the
ordered queue process. `V_cr(p)` of (9) is defined for `p > 0` only; at `p = 0` the paper's
bound `V_cr(0) ∧ 1 = 1` is the hypothesis `ρ < 1`, so the conclusion is guarded by `0 < p`.
Together with `ρ < 1` the conclusion is `ρ < V_cr(p) ∧ 1`; the boundary `ρ = V_cr(p)` is
excluded. -/
theorem theorem_2 (s : ℕ) (hs : 2 ≤ s) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (lam μ : ℝ) (hlam : 0 < lam) (hμ : 0 < μ) (hρ : lam / (s * μ) < 1)
    (hstab : StableNI s (pp2 s p) lam μ) :
    0 < p → lam / (s * μ) < Vcr s p := by sorry

end ParallelServerStab
