-- Prove2me | Theorems.Thm_ParallelServerStab_eq_15
-- name    : ParallelServerStab.eq_15
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:25:21.377366+00:00
-- url     : https://prove2.me/theorems/47d4b71e-0996-4a5d-af07-3d63939e50f9
-- title:
--   §5.3 and eq. (15) — the front server is ergodic with law $\pi^F$, busy with probability $\lambda/(\mu+\lambda p)$
-- statement:
--   Let $\lambda,\mu>0$, $p\in[0,1]$, and $\lambda(1-p)<\mu$. Let $Y^F$ be the birth–death process on $\mathbb Z_+$ with birth rate $\lambda$ and death rate $0$ at state $0$, and birth rate $\lambda(1-p)$ and death rate $\mu$ at every state $n\ge1$. Then:
--
--   1. $Y^F$ is ergodic: every state of its closed class — all of $\mathbb Z_+$ if $p<1$, and $\{0,1\}$ if $p=1$ — is recurrent with finite mean return time;
--   2. $\pi^F$, given by $\pi^F(0)=\dfrac{\mu-\lambda+\lambda p}{\mu+\lambda p}$ and $\pi^F(n)=\left(\dfrac{\lambda(1-p)}{\mu}\right)^{n-1}\dfrac{\lambda}{\mu}\pi^F(0)$ for $n\ge1$, is a stationary distribution of $Y^F$ (a probability distribution solving the global balance equations), and it is the only one;
--   3. the stationary probability that the front server is busy is
--
--   $$
--   \pi^F(\mathbb Z_+^*)=\sum_{n\ge1}\pi^F(n)=1-\pi^F(0)=\frac{\lambda}{\mu+\lambda p};
--   $$
--
--   4. for every $s\ge1$, with $\rho=\lambda/(s\mu)$, $\dfrac{\lambda}{\mu+\lambda p}=\dfrac{s\rho}{1+s\rho p}$.
--
--   In the proof of Theorem 2 the jobs that overflow the busy front server to the back servers arrive at rate $\lambda p\,\pi^F(\mathbb Z_+^*)$; comparing it with the back servers' capacity $(s-1)\mu$ gives the critical value.
--
--   Differences from the source:
--   - generalization: $p\in(1-1/s,1]$ and $\rho\in[V_{cr}(p),1)$ (standing assumptions of the proof of Theorem 2) → $\lambda,\mu>0$, $p\in[0,1]$, $\lambda(1-p)<\mu$; reason: the paper's assumptions imply $\lambda(1-p)=s\rho\mu(1-p)<\rho\mu<\mu$, so the statement specializes to the source's
--   - generalization: $\pi^F(i)=(\lambda(1-p)/\mu)^{i-1}(\lambda/\mu)\pi^F(0)$ for $i\ge2$ → the same formula for every $n\ge1$; reason: it holds at $n=1$ by the balance equation at $0$, and (15)'s $1-\pi^F(0)$ needs it there; the printed range is contained
--   - reading: $Y^F$ is ergodic → every state of the closed class of $0$ ($\mathbb Z_+$ for $p<1$, $\{0,1\}$ for $p=1$) is recurrent with finite mean return time; reason: for $p<1$ the chain is irreducible and this is ergodicity on $\mathbb Z_+$; for $p=1$ there are no births above $1$, so the states $n\ge2$ are transient and the paper's claim holds on $\{0,1\}$
--   - reading: $Y^F$ has stationary distribution $\pi^F$ → a sequence is a stationary distribution (probability solution of the balance equations, published `IsSteadyState`) if and only if it is $\pi^F$; reason: an ergodic chain has exactly one stationary distribution, which the paper calls the stationary distribution
--   - encoding: the CTMC $Y^F$; $\rho$ → its jump chain `frontJump` and exit rates `frontRate`; $\rho$ written $\lambda/(s\mu)$, for each $s\ge1$; reason: a CTMC without self-loops is determined by its jump chain and exit rates; the last identity holds for every $s$
-- source:
--   Moyal–Perry, Stability of Parallel Server Systems, arXiv:1904.10331v1, §5.3, display before (15) and eq. (15), p.14

import Mathlib
import Definitions.Def_ParallelServerStab_piF
import Definitions.Def_QueueingFundamentals_BirthDeath_Balance

namespace ParallelServerStab

open ProcessingNetworks.Stability QueueingFundamentals.BirthDeath

/-- The front server's stationary law and (15) (Moyal–Perry, Stability of Parallel Server
Systems, arXiv:1904.10331v1, §5.3, display before (15) and eq. (15), p. 14). Let `λ, µ > 0`,
`p ∈ [0, 1]` and `λ(1 − p) < µ` (which holds for the paper's `p ∈ (1 − 1/s, 1]`,
`ρ ∈ [V_cr(p), 1)`). The front-server process `Y^F` — the birth–death process on `ℤ₊` with
birth rate `λ` and death rate `0` at `0`, and birth rate `λ(1 − p)` and death rate `µ` at every
`n ≥ 1` — satisfies:
1. `Y^F` is ergodic: every state of its closed class (all of `ℤ₊` if `p < 1`, the states
   `{0, 1}` if `p = 1`) is recurrent with finite mean return time;
2. `π^F` is its stationary distribution, and the only one: a sequence solves the balance
   equations as a probability distribution iff it is `π^F`;
3. `π^F(ℤ*₊) = ∑_{n ≥ 1} π^F(n) = 1 − π^F(0)`, and `1 − π^F(0) = λ/(µ + λp)`;
4. `λ/(µ + λp) = sρ/(1 + sρp)` with `ρ = λ/(sµ)`, for every `s ≥ 1`.

**Formalization Note.** The CTMC `Y^F` is given by its jump chain `frontJump` and exit rates
`frontRate`; recurrence and mean return times are the published `ProcessingNetworks.Stability`
notions, and the stationary distribution is the published
`QueueingFundamentals.BirthDeath.IsSteadyState`. At `p = 1` the states `n ≥ 2` are transient
(no births above `1`), so ergodicity is stated on the closed class `{0, 1}`. -/
theorem eq_15 (lam μ p : ℝ) (hlam : 0 < lam) (hμ : 0 < μ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hload : lam * (1 - p) < μ) :
    (∀ n : ℕ, (p < 1 ∨ n ≤ 1) →
      Recurrent (frontJump lam μ p) n ∧
        meanReturnTime (frontJump lam μ p) (frontRate lam μ p) n < ⊤) ∧
    (∀ q : ℕ → ℝ, IsSteadyState (frontBirth lam p) (frontDeath μ) q ↔ q = piF lam μ p) ∧
    HasSum (fun n => piF lam μ p (n + 1)) (1 - piF lam μ p 0) ∧
    1 - piF lam μ p 0 = lam / (μ + lam * p) ∧
    ∀ s : ℕ, 1 ≤ s →
      lam / (μ + lam * p) = s * (lam / (s * μ)) / (1 + s * (lam / (s * μ)) * p) := by sorry

end ParallelServerStab
