-- Prove2me | Theorems.Thm_RSBeyondJohnson_FirstOrder_theorem_5_1
-- name    : RSBeyondJohnson.FirstOrder.theorem_5_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T16:31:53.643209+00:00
-- url     : https://prove2.me/theorems/c3185c74-b62f-4618-9c08-f0966ec2d42f
-- title:
--   Theorem 5.1 — first-order list decoding above the first-order curve
-- statement:
--   Fix $0<\rho<a<1$ with $a>a_1(\rho)$. Let $n\ge2$, $2\le k\le\rho n$ and $an\le A\le n$ be integers, choose $(m,B_\partial,B_{\mathrm{jet}},B_Z)$ by (28), and put $D=k-1$, $\lambda_{\mathrm{agr}}=(n-D)/(A-D)$. Let $F$ be a field of characteristic zero or $p>\max\{k-1,B_\partial\}$, with $n$ distinct evaluation points. Every received word $y\in F^n$ has finitely many polynomials of degree $<k$ with at least $A$ agreements, and
--   $$|\mathcal L(y,A)|\le4D\lambda_{\mathrm{agr}}B_{\mathrm{jet}}B_\partial+2B_{\mathrm{jet}}B_\partial+B_{\mathrm{jet}}=O_\rho\Big(\frac n{(\eta_1+1/n)^2}\Big)=O_\rho(n/\eta_1^2),\qquad(40)$$
--   where $\eta_1=a-a_1(\rho)$ and the constants of the $O_\rho$ depend on $\rho$ only.
--
--   Differences from the source:
--   - encoding: O_ρ(·) in (40) → ∀ ρ ∈ (0,1), ∃ C > 0 (chosen before every other variable), ∀ …: … ≤ C · (rate of the O); reason: the paper's convention (p. 5): the subscript lists the only parameters the hidden constant may depend on
--   - encoding: choose (m, B∂, B_jet, B_Z) by (28) → mParam, bDel, bJet, bZ ρ a n (definition Params); reason: the printed formulas of (28), as functions of (ρ, a, n) only
--   - encoding: field of characteristic zero or p > max{k − 1, B∂} → ringChar F = 0 ∨ max (k − 1) B∂ < ringChar F; reason: ringChar is the characteristic; same fields
--   - encoding: |L(y, A)| ≤ bound → (listDecodingSet k α y A).Finite ∧ ncard ≤ bound (reused RSListDecodingCapacity_AllRates_Decoding; zero polynomial included); reason: Set.ncard of an infinite set is 0; finiteness keeps the bound meaningful
--   - encoding: positions 1, …, n; distinct evaluation points α_1, …, α_n → Fin n (0-based); α : Fin n → F with Function.Injective α; reason: Lean indexing; the same instances
--   - encoding: every field F → every F : Type u (one universe, quantified inside the statement); reason: Lean universes; every field is isomorphic to one in the universe of its elements
--   - encoding: λ_agr = (n − D)/(A − D), D = k − 1 → lamAgr n (k − 1) A (real) and (k : ℝ) − 1; reason: exact real arithmetic
-- source:
--   Dao, Kominers, Thaler, Reed–Solomon Codes Beyond Johnson: Efficient Decoding and Smaller Cryptographic Proofs, STOC 2027 submission (manuscript of November 2, 2026, sha256 76a38731…), p. 30, Theorem 5.1

import Mathlib
import Definitions.Def_RSListDecodingCapacity_AllRates_Decoding
import Definitions.Def_RSBeyondJohnson_FirstOrder_Curve
import Definitions.Def_RSBeyondJohnson_FirstOrder_Params
import Definitions.Def_RSBeyondJohnson_FirstOrder_Counting

open Polynomial

namespace RSBeyondJohnson.FirstOrder

/-- **Theorem 5.1 (First-order list decoding above the first-order curve)**, p. 30. For every
rate `0 < ρ < 1` there is `C_ρ > 0` such that: for `ρ < a < 1` with `a > a₁(ρ)`, integers
`n ≥ 2`, `2 ≤ k ≤ ρn`, `an ≤ A ≤ n`, `(m, B∂, B_jet, B_Z)` from (28), `D = k − 1` and
`λ_agr = (n − D)/(A − D)`, the explicit bound
`4Dλ_agr B_jet B∂ + 2B_jet B∂ + B_jet` (40) is at most `C_ρ n/(η₁ + 1/n)²` and at most
`C_ρ n/η₁²` (`η₁ = a − a₁(ρ)`), and over every field `F` of characteristic zero or
`p > max{k − 1, B∂}` and all distinct evaluation points, every received word `y` has a finite
list `L(y, A)` of size at most that bound. -/
theorem theorem_5_1.{u} :
    ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∃ C : ℝ, 0 < C ∧
      ∀ (a : ℝ) (n k A : ℕ), ρ < a → a < 1 → a1 ρ < a → 2 ≤ n → 2 ≤ k → (k : ℝ) ≤ ρ * n →
        a * n ≤ (A : ℝ) → A ≤ n →
        (4 * ((k : ℝ) - 1) * lamAgr n (k - 1) A * bJet ρ a n * bDel ρ a n +
            2 * (bJet ρ a n : ℝ) * bDel ρ a n + bJet ρ a n ≤
          C * n / (a - a1 ρ + 1 / (n : ℝ)) ^ 2) ∧
        (4 * ((k : ℝ) - 1) * lamAgr n (k - 1) A * bJet ρ a n * bDel ρ a n +
            2 * (bJet ρ a n : ℝ) * bDel ρ a n + bJet ρ a n ≤
          C * n / (a - a1 ρ) ^ 2) ∧
        ∀ (F : Type u) [Field F], (ringChar F = 0 ∨ max (k - 1) (bDel ρ a n) < ringChar F) →
          ∀ α : Fin n → F, Function.Injective α → ∀ y : Fin n → F,
            (RSListDecodingCapacity.AllRates.listDecodingSet k α y (A : ℝ)).Finite ∧
            ((RSListDecodingCapacity.AllRates.listDecodingSet k α y (A : ℝ)).ncard : ℝ) ≤
              4 * ((k : ℝ) - 1) * lamAgr n (k - 1) A * bJet ρ a n * bDel ρ a n +
                2 * (bJet ρ a n : ℝ) * bDel ρ a n + bJet ρ a n := by sorry

end RSBeyondJohnson.FirstOrder
