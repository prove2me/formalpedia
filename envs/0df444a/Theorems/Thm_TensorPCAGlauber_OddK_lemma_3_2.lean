-- Prove2me | Theorems.Thm_TensorPCAGlauber_OddK_lemma_3_2
-- name    : TensorPCAGlauber.OddK.lemma_3_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T14:53:40.902372+00:00
-- url     : https://prove2.me/theorems/91589bf3-821a-484f-9ffe-eb4ae644b843
-- title:
--   Lemma 3.2 — Stein's lemma for the hypercube
-- statement:
--   For every $N$ and every $f:\Omega_N\to\mathbb R$, with $x\sim\pi$ uniform on the hypercube,
--   $$E_\pi[\nabla_\Omega f(x)]=E_\pi[xf(x)],\qquad E_\pi[\nabla^2_\Omega f(x)]=\tfrac12E_\pi\big[x\nabla_\Omega f(x)^\top+\nabla_\Omega f(x)x^\top\big]=E_\pi\big[(xx^\top-I)f(x)\big].$$
--   The identities are stated entrywise: the $i$-th entry of the first is $E_\pi[\partial_if]=E_\pi[x_if]$, and the $(i,j)$ entry of the second is $E_\pi[\partial_i\partial_jf]=\frac12E_\pi[x_i\partial_jf+\partial_if\,x_j]=E_\pi[(x_ix_j-\delta_{ij})f]$. This is the hypercube analogue of Gaussian integration by parts; it identifies the average discrete gradient with the first Fourier level and is used throughout the paper.
--
--   Differences from the source:
--   - encoding: $\Omega_N=\{\pm1\}^N$ → `Cube N = Fin N → Bool` with `true` ↦ +1, `false` ↦ −1 (`vec x` is the ±1 vector); reason: Lean convention; a bijection, same instances
-- source:
--   Das & Schramm, Averaged Annealed Markov Chains Achieve the Algorithmic Threshold for Tensor PCA, Part I: Glauber Dynamics, arXiv:2610.16705 (PDF of 2026-11-03, sha256 b1d9d241…), p. 16 (PDF 19), Lemma 3.2

import Mathlib
import Definitions.Def_TensorPCAGlauber_OddK_Hypercube

open MeasureTheory ProbabilityTheory

namespace TensorPCAGlauber.OddK

/-- **Lemma 3.2** (Stein's lemma for the hypercube). For every `f : Ω_N → ℝ`:
`E_π[∇_Ω f(x)] = E_π[x f(x)]` and
`E_π[∇²_Ω f(x)] = ½ E_π[x ∇_Ω f(x)ᵀ + ∇_Ω f(x) xᵀ] = E_π[(x xᵀ − I) f(x)]`, entrywise. -/
theorem lemma_3_2 (N : ℕ) (f : Cube N → ℝ) :
    (∀ i : Fin N, avg (fun x => pderiv i f x) = avg (fun x => vec x i * f x)) ∧
    (∀ i j : Fin N,
      avg (fun x => pderiv i (pderiv j f) x)
          = (1 / 2) * avg (fun x => vec x i * pderiv j f x + pderiv i f x * vec x j) ∧
      avg (fun x => pderiv i (pderiv j f) x)
          = avg (fun x => (vec x i * vec x j - if i = j then 1 else 0) * f x)) := by sorry

end TensorPCAGlauber.OddK
