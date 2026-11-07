-- Prove2me | Theorems.Thm_PolySampIso_lemma_32
-- name    : PolySampIso.lemma_32
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:29:29.509669+00:00
-- url     : https://prove2.me/theorems/b5ba30f1-318a-44c0-9c0e-4cbec6888e75
-- title:
--   Lemma 32, p.45 — defective variance contraction of Algorithm 6 (BackwardsMRW)
-- statement:
--   There is a universal constant $C>0$ with the following property. Let $X$ be a nonempty bounded polytope in $\mathbb R^n$, $\tau,N\in\mathbb N$, $t\ge0$, $\gamma\in\mathbb R^m_{>0}$, and $K(x,\cdot)=\mathrm{Law}(\mathrm{BackwardsMRW}(x,\gamma,\tau,t,N))$ the kernel of Algorithm 6. Write $\mu=\pi^{X|\Gamma=\gamma}_{t,\tau}$. Then for every bounded measurable $h:X\to\mathbb R$
--
--   $$\mathrm{Var}_\mu[Kh]\le\exp\Big(-\frac N{Cn}\Big)\mathrm{Var}_\mu[h]+2\,\mu\big(X\setminus B_\tau(\gamma,\tfrac14)\big)\,\mathrm{osc}(h)^2.$$
--
--   Run for $N=\Theta(n\log(1/\epsilon))$ steps, the whitened random walk contracts variance like an exact backwards step, except for a defect governed by the mass of the unstable region. The defect is not uniformly small, but it is small on average over $\gamma$ (Lemma 30).
--
--   Differences from the source:
--   - encoding: there is a universal constant C > 0 → ∃ C > 0 chosen before m, n, A, b, τ, N, t, γ, h; reason: universal means independent of every instance parameter
--   - encoding: bounded h : X → ℝ → measurable h : ℝⁿ → ℝ bounded on X; reason: functions are measurable by standing convention; values off X do not enter (K stays in X and µ lives on X)
--   - encoding: K(x, ·) := Law(BackwardsMRW(x, γ, τ, t, N)) → the kernel of the randomized map of Algorithm 6 driven by i.i.d. (fair coin, N(0, I_n), Unif[0, 1]) noise; reason: W ∼ Unif([2]) is the coin; 'with probability p' is 'u < p'
--   - encoding: τ, N ∈ N → τ ≥ 1, N ≥ 1; reason: the paper's N starts at 1
--   - encoding: the standing assumption of §2.3 (a nonempty, full-dimensional, bounded polytope; A full-rank) → X = {Ax < b} nonempty and bounded, n ≥ 1; reason: X is open, so nonempty means full-dimensional; nonempty and bounded imply full column rank
-- source:
--   Gu, Shi, Tian, Yang, Polytope Sampling at the Speed of Isoperimetry, arXiv:2610.23775 (preprint, sha256 b6a79179…), Lemma 32, p.45 (PDF p.47)

import Mathlib
import Definitions.Def_PolySampIso_Divergences
import Definitions.Def_PolySampIso_MarkovKernel
import Definitions.Def_PolySampIso_LogBarrier
import Definitions.Def_PolySampIso_DualConditioning
import Definitions.Def_PolySampIso_BackwardsMRW

open MeasureTheory ProbabilityTheory

namespace PolySampIso

/-- **Lemma 32** (defective variance contraction of Algorithm 6).

A. Gu, B. Shi, K. Tian, H. Yang, *Polytope Sampling at the Speed of Isoperimetry*,
arXiv:2610.23775 (preprint, sha256 b6a79179…), Lemma 32, p.45 (PDF p.47):

"Lemma 32. Let τ, N ∈ N, t ≥ 0, γ ∈ Rm>0, and let K(x, ·) := Law (BackwardsMRW(x, γ, τ, t, N))
denote the Markov kernel corresponding to Algorithm 6. There is a universal constant C > 0 such
that, for every bounded h : X → R,
VarπX|Γ=γt,τ[Kh] ≤ exp(−N/(Cn)) VarπX|Γ=γt,τ[h] + 2πX|Γ=γt,τ(X \ Bτ(γ, 1/4)) osc(h)²."

**Formalization Note.** `C` is chosen before all instance data (universal). `K = backwardsMRW`,
`π^{X|Γ=γ}_{t,τ} = condX` (55), `B_τ = stableSet` (57), `Kh = kapply K h`; `Var` is `variance`
and `osc` the essential oscillation, both under `π^{X|Γ=γ}_{t,τ}`. `h` is bounded on `X` and
measurable (standing convention); its values off `X` do not matter. `τ, N ∈ N` are `≥ 1`. The
standing assumption of §2.3 is kept. -/
theorem lemma_32 :
    ∃ C : ℝ, 0 < C ∧
      ∀ {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ), StandingAssumption A b →
        0 < n → ∀ τ N : ℕ, 1 ≤ τ → 1 ≤ N → ∀ t : ℝ, 0 ≤ t →
        ∀ γ : Fin m → ℝ, (∀ i, 0 < γ i) →
        ∀ h : EuclideanSpace ℝ (Fin n) → ℝ, Measurable h →
          (∃ M, ∀ x ∈ polytope A b, |h x| ≤ M) →
          variance (kapply (backwardsMRW A b γ τ t N) h) (condX A b t τ γ) ≤
            Real.exp (-(N : ℝ) / (C * n)) * variance h (condX A b t τ γ) +
              2 * (condX A b t τ γ).real (polytope A b \ stableSet A b τ γ (1 / 4)) *
                osc h (condX A b t τ γ) ^ 2 := by sorry

end PolySampIso
