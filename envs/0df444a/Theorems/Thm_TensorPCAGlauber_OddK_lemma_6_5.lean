-- Prove2me | Theorems.Thm_TensorPCAGlauber_OddK_lemma_6_5
-- name    : TensorPCAGlauber.OddK.lemma_6_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T14:55:32.298115+00:00
-- url     : https://prove2.me/theorems/3208490a-1678-493a-8b09-72a7a76f3606
-- title:
--   Lemma 6.5 — $H_0=\langle\zeta,x\rangle+H_0^\perp$ with $H_0^\perp$ a centered Gaussian process independent of $\zeta$
-- statement:
--   Let $k\ge3$ be odd, $N\ge1$ and $\zeta=E_\pi[\nabla_\Omega H_0]$. Then $H_0(x)=\langle\zeta,x\rangle+H_0^\perp(x)$, where $H_0^\perp:\Omega_N\to\mathbb R$ is a centered Gaussian process (every finite linear combination $\sum_xa_xH_0^\perp(x)$ is a centered normal variable), independent of $\zeta$, with
--   $$E\big[H_0^\perp(x)H_0^\perp(y)\big]=N\Big(\frac{\langle x,y\rangle}N\Big)^k-\sigma_N^2\langle x,y\rangle .$$
--   It shows that the average gradient sees only the first Fourier level of the disorder, independent of the bulk.
--
--   Differences from the source:
--   - encoding: $\Omega_N=\{\pm1\}^N$ → `Cube N = Fin N → Bool` with `true` ↦ +1, `false` ↦ −1 (`vec x` is the ±1 vector); reason: Lean convention; a bijection, same instances
--   - encoding: "$H_0^\perp$ is a centered Gaussian process" → every linear combination $\sum_xa_xH_0^\perp(x)$ has law `gaussianReal 0 v` for some $v\ge0$; reason: the index set $\Omega_N$ is finite, so this is joint Gaussianity
--   - encoding: the covariance identity → integrability of $H_0^\perp(x)H_0^\perp(y)$ is asserted together with the value of its integral; reason: no Bochner-integral junk value
--   - encoding: $N$ a dimension → hypothesis $1\le N$ (or $N\ge N_0$); reason: excludes only zero dimension, where $N^{-1}$ and $t/N$ are undefined
-- source:
--   Das & Schramm, Averaged Annealed Markov Chains Achieve the Algorithmic Threshold for Tensor PCA, Part I: Glauber Dynamics, arXiv:2610.16705 (PDF of 2026-11-03, sha256 b1d9d241…), p. 43 (PDF 46), Lemma 6.5

import Mathlib
import Definitions.Def_TensorPCAGlauber_OddK_Hypercube
import Definitions.Def_TensorPCAGlauber_OddK_Model
import Definitions.Def_TensorPCAGlauber_OddK_Gauge

open MeasureTheory ProbabilityTheory

namespace TensorPCAGlauber.OddK

/-- **Lemma 6.5** (Decomposition of the `k`-spin Hamiltonian). For odd `k ≥ 3` and
`ζ = E_π[∇_Ω H_0]`: `H_0(x) = ⟨ζ, x⟩ + H_0^⊥(x)`, where `H_0^⊥` is a centered Gaussian process
independent of `ζ` with `E[H_0^⊥(x) H_0^⊥(y)] = N(⟨x,y⟩/N)^k − σ²_N⟨x,y⟩`. -/
theorem lemma_6_5 (k : ℕ) (hk : 3 ≤ k) (hodd : Odd k) (N : ℕ) (hN : 1 ≤ N) :
    (∀ (G' : KTensor k N) (x : Cube N),
        H0 k N G' x = dot (zeta k N G') (vec x) + H0perp k N G' x) ∧
    (∀ a : Cube N → ℝ, ∃ v : NNReal,
        (disorderMeasure k N).map (fun G' => ∑ x, a x * H0perp k N G' x) = gaussianReal 0 v) ∧
    IndepFun (zeta k N) (H0perp k N) (disorderMeasure k N) ∧
    (∀ x y : Cube N,
        Integrable (fun G' => H0perp k N G' x * H0perp k N G' y) (disorderMeasure k N) ∧
        ∫ G', H0perp k N G' x * H0perp k N G' y ∂(disorderMeasure k N)
          = N * (dot (vec x) (vec y) / N) ^ k - sigmaSq k N * dot (vec x) (vec y)) := by sorry

end TensorPCAGlauber.OddK
