-- Prove2me | Theorems.Thm_QGradGAW_Smooth_central_coeff_moments
-- name    : QGradGAW.Smooth.central_coeff_moments
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T17:28:46.616983+00:00
-- url     : https://prove2.me/theorems/203a659d-12c1-48a6-8150-d8ebbd305c75
-- title:
--   Proof of Theorem 24, p. 54 — Σ_{ℓ=−m}^{m} a_ℓ^(2m) ℓᵏ is 1 for k = 1 and 0 for the other k ≤ 2m
-- statement:
--   For every $m\in\mathbb N$ and every integer $0\le k\le 2m$,
--   $$\sum_{\ell=-m}^{m}a_\ell^{(2m)}\,\ell^{k}=\begin{cases}1,&k=1,\\[2pt]0,&k\neq1,\end{cases}$$
--   with the convention $0^0=1$.
--
--   Equivalently, the central difference formula $f_{(2m)}$ is exact on polynomials of degree at most $2m$: it returns the derivative at $0$. In the proof of Theorem 24 this kills every Taylor term of degree $\le 2m$ except the linear one.
-- source:
--   Gilyén, Arunachalam, Wiebe, Optimizing quantum optimization algorithms via faster quantum gradient computation, arXiv:1711.00465v3, p. 54, proof of Theorem 24 (the sum (∗) and the sentence after it)

import Mathlib
import Definitions.Def_QGradGAW_Smooth_Setting

namespace QGradGAW.Smooth

/-- arXiv:1711.00465v3, p. 54, proof of Theorem 24 (Lemma 22 applied to `x^k` with `δ = 1`):
for `k ≤ 2m`, `Σ_{ℓ=−m}^{m} a_ℓ^(2m) ℓ^k` is `1` if `k = 1` and `0` otherwise
(with `0^0 = 1`). -/
theorem central_coeff_moments (m k : ℕ) (hk : k ≤ 2 * m) :
    ∑ ℓ ∈ Finset.Icc (-(m : ℤ)) m, centralCoeff m ℓ * (ℓ : ℝ) ^ k = if k = 1 then 1 else 0 := by sorry

end QGradGAW.Smooth
