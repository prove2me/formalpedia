-- Prove2me | Theorems.Thm_ParallelServerStab_overflow_iff
-- name    : ParallelServerStab.overflow_iff
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:25:14.852212+00:00
-- url     : https://prove2.me/theorems/5830ce28-5b8a-4c93-81c3-c7eb87cb0662
-- title:
--   §5.3, before (19) — $\rho>V_{cr}(p)$ if and only if the overflow rate $\lambda p\,\pi^F(\mathbb Z_+^*)$ exceeds $(s-1)\mu$
-- statement:
--   Let $s\ge2$, $p\in(0,1]$, $\lambda,\mu>0$ and $\rho=\lambda/(s\mu)$. Then
--
--   $$
--   \rho>V_{cr}(p)\iff \lambda p\,\pi^F(\mathbb Z_+^*)>(s-1)\mu,
--   $$
--
--   where $\pi^F(\mathbb Z_+^*)=1-\pi^F(0)$ is the stationary probability that the front server is busy.
--
--   The left side of the right-hand inequality is the rate at which jobs overflow from the busy front server to the $s-1$ back servers; the right side is the back servers' total service capacity. Above the critical value the back servers are overloaded.
--
--   Differences from the source:
--   - reading: $s \ge 1$ servers in (9), $s$ servers in §3 → $s \ge 2$; reason: the model has $s \ge 2$ servers (§1, p. 1), $p_{p,2}=(1-p,p,0,\dots,0)$ needs two coordinates, and (9) divides by $p(s-1)$
--   - generalization: $p\in(1-1/s,1]$ and $\rho\in[V_{cr}(p),1)$ (standing assumptions of the proof) → every $p\in(0,1]$ and $\lambda,\mu>0$; reason: the equivalence is algebraic; the source's range is contained
--   - encoding: $\pi^F(\mathbb Z_+^*)$ → $1-\pi^F(0)$; reason: (15) states $\pi^F(\mathbb Z_+^*)=1-\pi^F(0)$
--   - reading: $V_{cr}(p,2)$ → $V_{cr}(p)$ of (9); reason: the paper writes $V_{cr}(p,2)$, $V_{cr}(p,s)$ and $V_{cr}(p)$ for the same number in §5.3
-- source:
--   Moyal–Perry, Stability of Parallel Server Systems, arXiv:1904.10331v1, §5.3, proof of Theorem 2, sentence before (19), p.15

import Mathlib
import Definitions.Def_ParallelServerStab_Vcr
import Definitions.Def_ParallelServerStab_piF

namespace ParallelServerStab

/-- The overflow exceeds the back servers' capacity exactly above the critical value
(Moyal–Perry, Stability of Parallel Server Systems, arXiv:1904.10331v1, §5.3, sentence before
(19), p. 15: "`ρ > V_cr(p, 2)` if and only if `λpπ^F(ℤ*₊) > (s − 1)µ`"). For `s ≥ 2`,
`p ∈ (0, 1]`, `λ, µ > 0` and `ρ = λ/(sµ)`:
`V_cr(p) < ρ ↔ (s − 1)µ < λ p π^F(ℤ*₊)`, with `π^F(ℤ*₊) = 1 − π^F(0)`.

**Formalization Note.** `π^F(ℤ*₊)` is written `1 − π^F(0)`, as in (15); `V_cr(p, 2)` is the
`V_cr(p)` of (9). The equivalence is algebraic and holds without the paper's standing
assumptions `p > 1 − 1/s`, `ρ ∈ [V_cr(p), 1)`. -/
theorem overflow_iff (s : ℕ) (hs : 2 ≤ s) (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) (lam μ : ℝ)
    (hlam : 0 < lam) (hμ : 0 < μ) :
    Vcr s p < lam / (s * μ) ↔ ((s : ℝ) - 1) * μ < lam * p * (1 - piF lam μ p 0) := by sorry

end ParallelServerStab
