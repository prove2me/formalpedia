-- Prove2me | Theorems.Thm_SuperRamanujan227_Main_theorem_5_7
-- name    : SuperRamanujan227.Main.theorem_5_7
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-08T09:35:25.233047+00:00
-- url     : https://prove2.me/theorems/600c7f81-87d5-4838-b72d-84c9460e11a4
-- title:
--   Theorem 5.7 — Krasikov's bound on the largest zero of $P_r^{(\gamma,\gamma)}$
-- statement:
--   Let $r\ge1$ be an integer and $\gamma>-1$ real, and let $z_{r,\gamma}$ be the largest zero of the symmetric Jacobi polynomial $P_r^{(\gamma,\gamma)}$. Define
--   $$s=2\gamma+1,\qquad \rho=2r+2\gamma+1,\qquad R=\sqrt{(\rho^2+2s+1)(\rho^2-s^2)},\qquad B=\frac{R}{\rho^2+2s+1}.$$
--   Then
--   $$z_{r,\gamma}<B-3\,(1-B^2)^{2/3}(2R)^{-1/3}.$$
--
--   This is the symmetric specialization of Krasikov's bound [Kra06, Theorem 2]; applied with $r=n$ and $\gamma=n(d-2)/2$ it yields Claim 5.6. The parameter $\gamma$ ranges over all reals greater than $-1$, not only integers or half-integers.
--
--   **Formalization Note** $(1-B^2)^{2/3}$ and $(2R)^{-1/3}$ are real powers of positive numbers (for $\gamma>-1$ one has $0<B<1$ and $R>0$).
--
--   Differences from the source:
--   - reading: z_{r,γ} the largest zero of P_r^(γ,γ), r not further restricted → r ≥ 1; reason: a largest zero presupposes positive degree; the degree-0 polynomial is a nonzero constant with no zero
--   - encoding: P_r^(γ,γ) → classical normalization of the Jacobi polynomial; z_{r,γ} its largest real root; reason: roots do not depend on the normalization
-- source:
--   Gil Cohen, Gal Maor, Quantitative Results on Super-Ramanujan Graphs, STOC 2027 submission #227 (October 2026), SHA-256 1ba5eacb267c8a63eff5e5b9d6b96d9f2b04d5a1e147d887b9e61574127831f8, Theorem 5.7 (symmetric case of [Kra06, Theorem 2]), p. 20

import Mathlib
import Definitions.Def_SuperRamanujan227_Main_Spectra
import Definitions.Def_SuperRamanujan227_Main_Jacobi
open Polynomial

namespace SuperRamanujan227.Main

/-- Theorem 5.7 (Krasikov's bound, symmetric case, p. 20): for `r ≥ 1` and real `γ > -1`, with
`s = 2γ + 1`, `ρ = 2r + 2γ + 1`, `R = √((ρ² + 2s + 1)(ρ² - s²))` and `B = R / (ρ² + 2s + 1)`, the
largest zero `z_{r,γ}` of `P_r^{(γ,γ)}` satisfies `z_{r,γ} < B - 3 (1 - B²)^{2/3} (2R)^{-1/3}`. -/
theorem theorem_5_7 (r : ℕ) (hr : 1 ≤ r) (γ : ℝ) (hγ : -1 < γ) :
    let s : ℝ := 2 * γ + 1
    let ρ : ℝ := 2 * (r : ℝ) + 2 * γ + 1
    let R : ℝ := Real.sqrt ((ρ ^ 2 + 2 * s + 1) * (ρ ^ 2 - s ^ 2))
    let B : ℝ := R / (ρ ^ 2 + 2 * s + 1)
    kthLargestRoot (jacobiSym γ r) 1 <
      B - 3 * (1 - B ^ 2) ^ ((2 : ℝ) / 3) * (2 * R) ^ (-(1 : ℝ) / 3) := by sorry

end SuperRamanujan227.Main
