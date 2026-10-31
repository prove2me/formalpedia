-- Prove2me | Theorems.Thm_ParallelServerStab_eq_16
-- name    : ParallelServerStab.eq_16
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:25:53.986539+00:00
-- url     : https://prove2.me/theorems/d1cc2fcd-fdbf-4c1b-8489-50b3668735b7
-- title:
--   Eq. (16) — the front server converges to $\pi^F$ exponentially fast in total variation
-- statement:
--   Let $\lambda,\mu>0$, $p\in[0,1]$, and $\lambda(1-p)<\mu$, and let $Y^F$ be the front-server birth–death process of (15) with stationary law $\pi^F$. There is $\beta>0$, independent of the initial condition, such that for every initial state $y\in\mathbb Z_+$ there is $C_0\in[0,\infty)$, depending on $y$ only, with
--
--   $$
--   \big\|P(Y^F(t)\in\cdot)-\pi^F(\cdot)\big\|_{TV}<C_0e^{-\beta t}\qquad\text{for all } t\ge0,
--   $$
--
--   where $Y^F(0)=y$. Here $\|\nu-\pi\|_{TV}=\sup_A|\nu(A)-\pi(A)|$.
--
--   The proof of Theorem 2 uses this bound to show that after a fixed time, uniformly over the visits that start with an empty front server, the front server is busy at arrival epochs with probability close to $\pi^F(\mathbb Z_+^*)$.
--
--   **Formalization Note** $Y^F$ is realized by uniformization at rate $\lambda+\mu$: a Markov chain with the uniformized kernel, started at $y$, run at the epochs of an independent Poisson clock of rate $\lambda+\mu$ (published `IsUniformizedProcess`, with `jumpPath` the state at time $t$). The statement holds for every such realization on every probability space. The total-variation distance is the published `MarkovChainCLT.tvDist`.
--
--   Differences from the source:
--   - generalization: $p\in(1-1/s,1]$ and $\rho\in[V_{cr}(p),1)$ (standing assumptions of the proof of Theorem 2) → $\lambda,\mu>0$, $p\in[0,1]$, $\lambda(1-p)<\mu$; reason: the paper's assumptions imply $\lambda(1-p)=s\rho\mu(1-p)<\rho\mu<\mu$, so the statement specializes to the source's
--   - reading: $\pi(\cdot)$ in (16) → $\pi^F$; reason: the stationary law of $Y^F$, as in (17)
--   - encoding: the continuous-time BD process $Y^F$ started at $y$ → every uniformized realization (kernel `frontKernel`, Poisson clock of rate $\lambda+\mu$) on every probability space; the law of $Y^F(t)$ through its point masses; reason: uniformization at a rate bounding all exit rates is the standard construction of a bounded-rate CTMC; for a measurable variable the point-mass law is its distribution
--   - encoding: $\|\cdot\|_{TV}$, the total-variation norm → $\sup_A|\nu(A)-\pi(A)|$ (published `MarkovChainCLT.tvDist`); reason: it is half of the total-variation norm, and the factor $2$ is absorbed by the free constant $C_0$
-- source:
--   Moyal–Perry, Stability of Parallel Server Systems, arXiv:1904.10331v1, eq. (16), p.14

import Mathlib
import Definitions.Def_ParallelServerStab_piF
import Definitions.Def_StrictCompatLB_MeanField_CountableChain
import Definitions.Def_TotalVariationDist

universe u

namespace ParallelServerStab

open MeasureTheory StrictCompatLB.MeanField

/-- (16): the front server is exponentially ergodic (Moyal–Perry, Stability of Parallel Server
Systems, arXiv:1904.10331v1, eq. (16), p. 14). Let `λ, µ > 0`, `p ∈ [0, 1]` and
`λ(1 − p) < µ`. There is `β > 0`, independent of the initial condition, such that for every
initial state `y` there is `C₀ ∈ [0, ∞)`, depending on `y` only, with
`‖P(Y^F(t) ∈ ·) − π^F(·)‖_TV < C₀ e^{−βt}` for all `t ≥ 0`, where `Y^F` is the front-server
birth–death process started at `y`.

**Formalization Note.** `Y^F` is realized by uniformization at clock rate `λ + µ`: a Markov
chain with kernel `frontKernel` run at the epochs of an independent rate-`(λ + µ)` Poisson
clock (`IsUniformizedProcess`), its state at time `t` being `jumpPath`; this is the standard
construction of a bounded-rate CTMC, and the statement quantifies over every such realization
on every probability space in universe `u`. The law of `Y^F(t)` is `lawNat` (point masses
`P(Y^F(t) = n)`). The total-variation distance is the published `MarkovChainCLT.tvDist`,
`sup_A |ν(A) − π(A)|`, half the `ℓ¹` norm; the factor `2` is absorbed by the free constant
`C₀`. -/
theorem eq_16 (lam μ p : ℝ) (hlam : 0 < lam) (hμ : 0 < μ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hload : lam * (1 - p) < μ) :
    ∃ β : ℝ, 0 < β ∧ ∀ y : ℕ, ∃ C₀ : ℝ, 0 ≤ C₀ ∧
      ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (Y : ℕ → Ω → ℕ) (τ : ℕ → Ω → ℝ),
        IsUniformizedProcess P (frontKernel lam μ p) (lam + μ) y Y τ →
        ∀ t : ℝ, 0 ≤ t →
          MarkovChainCLT.tvDist
              (lawNat P (fun ω => jumpPath (fun n => Y n ω) (fun k => τ k ω) t))
              (piFMeasure lam μ p) <
            C₀ * Real.exp (-β * t) := by sorry

end ParallelServerStab
