-- Prove2me | Theorems.Thm_TensorPCAGlauber_OddK_lemma_3_6
-- name    : TensorPCAGlauber.OddK.lemma_3_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T14:54:34.830293+00:00
-- url     : https://prove2.me/theorems/6f9e64f1-4741-4d4f-b458-56a4560cfa13
-- title:
--   Lemma 3.6 — Sobolev-norm concentration of the pure $k$-spin Hamiltonian $H_0$
-- statement:
--   Let $H_0(x)=N^{-(k-1)/2}\langle G,x^{\otimes k}\rangle$ be the Ising pure $k$-spin Hamiltonian, $G$ the symmetrized Gaussian $k$-tensor ($k\ge3$). For every integer $n\ge0$ there are constants $C_{k,n},c_{k,n}>0$, depending only on $k$ and $n$, such that for every $N\ge1$ and every $t\ge0$,
--   $$P\Big[\|H_0\|_{D^n}\ge C_{k,n}N\Big(1+\sqrt{t/N}\Big)\Big]\le\exp\big(-c_{k,n}(N+t)\big).$$
--   Here $\|\cdot\|_{D^n}$ is the discrete Sobolev norm of Definition 3.5, built from operator norms of the discrete derivative tensors. The lemma controls the regularity of the disorder and feeds the ergodic-average and dynamics estimates.
--
--   Differences from the source:
--   - encoding: $\Omega_N=\{\pm1\}^N$ → `Cube N = Fin N → Bool` with `true` ↦ +1, `false` ↦ −1 (`vec x` is the ±1 vector); reason: Lean convention; a bijection, same instances
--   - encoding: $N$ a dimension → hypothesis $1\le N$ (or $N\ge N_0$); reason: excludes only zero dimension, where $N^{-1}$ and $t/N$ are undefined
--   - encoding: $P[\text{good event}]\ge 1-\varepsilon$ → the (outer) measure of the complementary bad event is $\le\varepsilon$; reason: equivalent for measurable events, and never weaker
-- source:
--   Das & Schramm, Averaged Annealed Markov Chains Achieve the Algorithmic Threshold for Tensor PCA, Part I: Glauber Dynamics, arXiv:2610.16705 (PDF of 2026-11-03, sha256 b1d9d241…), p. 18 (PDF 21), Lemma 3.6

import Mathlib
import Definitions.Def_TensorPCAGlauber_OddK_Hypercube
import Definitions.Def_TensorPCAGlauber_OddK_Model

open MeasureTheory ProbabilityTheory

namespace TensorPCAGlauber.OddK

/-- **Lemma 3.6** (Sobolev norm concentration for the Ising pure `k`-spin Hamiltonian). For every
integer `n ≥ 0` there are `C_{k,n}, c_{k,n} > 0` such that for every `N ≥ 1` and every `t ≥ 0`,
`P[‖H_0‖_{D^n} ≥ C_{k,n} N (1 + √(t/N))] ≤ exp(−c_{k,n}(N + t))`. -/
theorem lemma_3_6 (k : ℕ) (hk : 3 ≤ k) (n : ℕ) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ N : ℕ, 1 ≤ N → ∀ t : ℝ, 0 ≤ t →
        disorderMeasure k N
            {G' | C * N * (1 + Real.sqrt (t / N)) ≤ sobolevNorm n (H0 k N G')}
          ≤ ENNReal.ofReal (Real.exp (-(c * (N + t)))) := by sorry

end TensorPCAGlauber.OddK
