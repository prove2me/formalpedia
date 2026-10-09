-- Prove2me | Theorems.Thm_RelSmoothFOM_PrimalGrad_ck_identity
-- name    : RelSmoothFOM.PrimalGrad.ck_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:34:33.734876+00:00
-- url     : https://prove2.me/theorems/e883ec79-2a16-4478-8733-8d9284e29ae2
-- title:
--   Proof of Theorem 3.1, p. 345 — C_k := 1/Σᵢ(L/(L−μ))ⁱ = μ/(L((1+μ/(L−μ))ᵏ − 1)) for μ > 0, and C_k = 1/k for μ = 0
-- statement:
--   Let $0\le\mu<L$ and $k\ge1$, and define
--   $$C_k:=\frac{1}{\sum_{i=1}^k\big(\frac{L}{L-\mu}\big)^i}.$$
--   Then:
--
--   1. if $\mu>0$,
--   $$C_k=\frac{\mu}{L\Big(\big(1+\frac{\mu}{L-\mu}\big)^k-1\Big)};$$
--   2. if $\mu=0$, then $C_k=\dfrac1k$.
--
--   The parameter $C_k$ is the normalising constant that converts the weighted inequality (30) into the bound (31) on the optimality gap; the closed form follows from summing a geometric series.
--
--   **Formalization Note** The hypothesis $\mu<L$ is added because $C_k$ divides by $L-\mu$; $L>0$ and $k\ge1$ are where the paper uses $C_k$.
-- source:
--   Lu, Freund & Nesterov, Relatively smooth convex optimization by first-order methods, and applications, SIAM J. Optim. 28 (2018), p. 345, proof of Theorem 3.1, definition of C_k

import Mathlib
import Definitions.Def_RelSmoothFOM_PrimalGrad_Setting

namespace RelSmoothFOM.PrimalGrad

theorem ck_identity (L μ : ℝ) (hL : 0 < L) (hμ : 0 ≤ μ) (hμL : μ < L)
    (k : ℕ) (hk : 1 ≤ k) :
    (0 < μ → 1 / ∑ i ∈ Finset.Icc 1 k, (L / (L - μ)) ^ i
        = μ / (L * ((1 + μ / (L - μ)) ^ k - 1))) ∧
    (μ = 0 → 1 / ∑ i ∈ Finset.Icc 1 k, (L / (L - μ)) ^ i = 1 / (k : ℝ)) := by sorry

end RelSmoothFOM.PrimalGrad
