-- Prove2me | Theorems.Thm_ParallelServerStab_proposition_2
-- name    : ParallelServerStab.proposition_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:24:23.288391+00:00
-- url     : https://prove2.me/theorems/55ca09ce-e0c7-4960-994a-e52840483fc2
-- title:
--   Proposition 2 — under non-idling J2SQ, stability forces $\rho<V_{cr}(1)$; J2SQ$^{NI}$ is non-maximal
-- statement:
--   Consider $s\ge2$ servers under the non-idling join-the-second-shortest-queue policy J2SQ$^{NI}$: an arriving job joins an idle server if there is one, and otherwise joins the second-shortest queue (allocation vector $\mathbf p_{1,2}=(0,1,0,\dots,0)$). Then
--
--   1. for all $\lambda,\mu>0$ with $\rho=\lambda/(s\mu)<1$, if the system is stable, then $\rho<V_{cr}(1)$; that is,
--
--   $$
--   S^{NI}(\mathbf p_{1,2})\subseteq[0,V_{cr}(1));
--   $$
--
--   2. J2SQ$^{NI}$ is **non-maximal**: there are $\lambda,\mu>0$ with $\rho<1$ for which the system is not stable.
--
--   Since $V_{cr}(1)<1$, the usual traffic condition does not give stability under this non-idling policy. This is the case $p=1$ of Theorem 2.
--
--   **Formalization Note** Stability is positive recurrence of the empty state of the ordered queue process (`StableNI`).
--
--   Differences from the source:
--   - reading: $\subset$ → $\subseteq$; reason: strict inclusion would be false for $p \le 1-1/s$, where $V_{cr}(p)\wedge 1 = 1$ and $S^{NI}(p_{p,2})=[0,1)$ (Corollary 3); the paper uses $\subset$ for inclusion
--   - reading: $Q$ is a positive recurrent CTMC (§3.1, p. 8) → the empty state of the ordered chain is recurrent and its mean return time (holding times included) is finite; reason: the ordered chain is not irreducible on $\mathcal R(\mathbb Z_+^s)$ (under J2SQ$^{NI}$ the shortest queue never exceeds $1$ from the empty state), so positive recurrence of every state is false for every $\rho$; the paper argues from the empty state (Corollary 1)
--   - reading: $s \ge 1$ servers in (9), $s$ servers in §3 → $s \ge 2$; reason: the model has $s \ge 2$ servers (§1, p. 1), $p_{p,2}=(1-p,p,0,\dots,0)$ needs two coordinates, and (9) divides by $p(s-1)$
--   - encoding: $\rho \in S^{NI}(\mathbf p)$, a set of traffic intensities in $[0,1)$ → for all $\lambda,\mu>0$ with $\rho=\lambda/(s\mu)<1$, stability of the chain with these rates; reason: stability depends on $\lambda,\mu$ only through $\rho$; $\rho=0$ ($\lambda=0$) is left out, where the conclusion holds outright
--   - encoding: ordered queue vectors in $\mathcal R(\mathbb Z_+^s)$, ranks $1,\dots,s$, uniform labels inside tie blocks → monotone `Fin s → ℕ`, 0-based ranks; routing to rank $i$ adds the job at the last rank of $i$'s tie block, a departure from rank $i$ removes it at the first rank of the block; an arrival that finds idle servers joins one chosen uniformly; reason: after re-sorting every choice inside a tie block gives the same ordered state, so these are the paper's transitions
--   - encoding: the CTMC $Q$ → its jump chain `jumpNI` and exit rates `rateNI` $=\lambda+\mu\cdot\#\{\text{busy servers}\}$; reason: a CTMC with no self-loops is determined by its jump chain and exit rates
--   - encoding: non-maximal: $S^{NI}(\mathbf p_{1,2})\ne[0,1)$ (§4, p.8) → some $\lambda,\mu>0$ with $\rho<1$ for which the chain is not stable; reason: maximal means the stability region is $[0,1)$
-- source:
--   Moyal–Perry, Stability of Parallel Server Systems, arXiv:1904.10331v1, Proposition 2, p.11

import Mathlib
import Definitions.Def_ParallelServerStab_Vcr
import Definitions.Def_ParallelServerStab_StableNI

namespace ParallelServerStab

/-- Proposition 2 (Moyal–Perry, Stability of Parallel Server Systems, arXiv:1904.10331v1,
Proposition 2, p. 11): `S^NI(p_{1,2}) ⊆ [0, V_cr(1))`; in particular J2SQ^NI is non-maximal.
For `s ≥ 2` servers:
1. for all `λ, µ > 0` with `ρ = λ/(sµ) < 1`, if the parallel-server system under the
   non-idling join-the-second-shortest-queue policy is stable, then `ρ < V_cr(1)`;
2. there are `λ, µ > 0` with `ρ < 1` for which it is not stable.

**Formalization Note.** Stability (`StableNI`) is positive recurrence of the empty state of the
ordered queue process (jump chain `jumpNI`, exit rates `rateNI`); the paper's `⊂` is read as
`⊆`. -/
theorem proposition_2 (s : ℕ) (hs : 2 ≤ s) :
    (∀ lam μ : ℝ, 0 < lam → 0 < μ → lam / (s * μ) < 1 →
      StableNI s (p12 s) lam μ → lam / (s * μ) < Vcr s 1) ∧
    ∃ lam μ : ℝ, 0 < lam ∧ 0 < μ ∧ lam / (s * μ) < 1 ∧ ¬ StableNI s (p12 s) lam μ := by sorry

end ParallelServerStab
