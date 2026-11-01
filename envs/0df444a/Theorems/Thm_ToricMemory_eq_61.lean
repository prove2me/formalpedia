-- Prove2me | Theorems.Thm_ToricMemory_eq_61
-- name    : ToricMemory.eq_61
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:21:44.66739+00:00
-- url     : https://prove2.me/theorems/69a79469-84c9-4650-9c15-e06e2887b510
-- title:
--   Eqs. (60)–(61) — below threshold every term is at most $(4\mu_3^2\tilde p)^{L/2}$
-- statement:
--   Let $p,q\in[0,1]$, $\tilde p=p(1-p)$ and $\tilde q=q(1-q)$, and suppose
--   $$
--   \tilde p<(4\mu_3^2)^{-1},\qquad \tilde q<(4\mu_3^2)^{-1}. \tag{60}
--   $$
--   Then for all $H\ge L$ and all $V$,
--   $$
--   (4\mu_3^2\tilde p)^{H/2}(4\mu_3^2\tilde q)^{V/2}\;\le\;(4\mu_3^2\tilde p)^{L/2}. \tag{61}
--   $$
--
--   This turns the sum (59) into a polynomial number of terms each bounded by $(4\mu_3^2\tilde p)^{L/2}$.
--
--   Differences from the source:
--   - reading: μ₃ ≈ 4.684 (eq. (58)) → mu3 := inf_{n ≥ 1} c_n^{1/n}, the exact connective constant of ℤ³; reason: the decimal is the numerical value of the cubic lattice's connective constant, which is what the bound (58) is about
--   - generalization: every term appearing in the sum (59): L ≤ H ≤ 2L²T, V ≤ L²T → all natural numbers L ≤ H and all V; reason: the terms of the sum are among these
--   - encoding: (4μ₃²p̃), (4μ₃²q̃)^{·/2} powers → (√x)^n for x^{n/2}; reason: the same real number for x ≥ 0; avoids ℕ division in the exponent
-- source:
--   Dennis, Kitaev, Landahl & Preskill, Topological quantum memory, arXiv:quant-ph/0110143v1, Sec. V C, eqs. (60)–(61), p. 20

import Mathlib
import Definitions.Def_ToricMemory_CubicSAW

namespace ToricMemory

/-- **Eqs. (60)–(61)**, arXiv:quant-ph/0110143v1, Sec. V C, p. 20 (PDF p. 20): "Provided that
`p̃ < (4μ₃²)^{−1}`, `q̃ < (4μ₃²)^{−1}` (60) we have
`(4μ₃² p̃)^{H/2} · (4μ₃² q̃)^{V/2} ≤ (4μ₃² p̃)^{L/2}` (61) for every term appearing in the sum",
i.e. for every `H ≥ L` and every `V`. Here `p̃ = p(1 − p)`, `q̃ = q(1 − q)` with `p, q ∈ [0, 1]`.

**Formalization Note** `x^{H/2}` is written `(√x)^H`. -/
theorem eq_61 (p q : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hp : p * (1 - p) < 1 / (4 * mu3 ^ 2)) (hq : q * (1 - q) < 1 / (4 * mu3 ^ 2))
    (L H V : ℕ) (hH : L ≤ H) :
    Real.sqrt (4 * mu3 ^ 2 * (p * (1 - p))) ^ H * Real.sqrt (4 * mu3 ^ 2 * (q * (1 - q))) ^ V ≤
      Real.sqrt (4 * mu3 ^ 2 * (p * (1 - p))) ^ L := by sorry

end ToricMemory
