-- Prove2me | Theorems.Thm_RSBeyondJohnson_FirstOrder_theorem_5_2
-- name    : RSBeyondJohnson.FirstOrder.theorem_5_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T16:31:59.804837+00:00
-- url     : https://prove2.me/theorems/c2add579-9326-43fc-ba25-22a35ebb2db4
-- title:
--   Theorem 5.2 — first-order line MCA above the first-order curve
-- statement:
--   Fix $0<\rho<a<1$ with $a>a_1(\rho)$. Let $n\ge2$, $2\le k\le\rho n$, $an\le A\le n$ be integers, choose $(m,B_\partial,B_{\mathrm{jet}},B_Z)$ by (28), and put $D=k-1$, $\lambda_{\mathrm{agr}}=(n-D)/(A-D)$, $b=B_{\mathrm{jet}}(2B_\partial+1)$, $h=B_Z(2B_\partial+1)$. Let $F$ be a field of characteristic zero or $p>\max\{k-1,B_\partial\}$, with $n$ distinct evaluation points. For every received line $f+zg$ there is one exceptional set $\mathcal E$ with
--   $$|\mathcal E|\le(2b-1)h+\lambda_{\mathrm{agr}}(h+b+4Dbh)+(n-D-1)b+(48D^2B_Z+16D)\lambda_{\mathrm{agr}}^2B_{\mathrm{jet}}B_\partial+8D(n-D-1)\lambda_{\mathrm{agr}}B_{\mathrm{jet}}B_\partial$$
--   $$=O_\rho\Big(\frac{n^2}{(\eta_1+1/n)^4}\Big)=O_\rho(n^2/\eta_1^4)\qquad(41)$$
--   such that every $z\notin\mathcal E$ and every degree-$<k$ candidate $P$ with $|S_z(P)|\ge A$ admit degree-$<k$ witnesses $F_0,G_0$ with $P=F_0+zG_0$ and $S_z(P)=S(F_0,G_0)$.
--
--   Differences from the source:
--   - encoding: O_ρ(·) in (41) → ∀ ρ ∈ (0,1), ∃ C > 0 (chosen before every other variable), ∀ …: … ≤ C · (rate of the O); reason: the paper's convention (p. 5): the subscript lists the only parameters the hidden constant may depend on
--   - encoding: choose (m, B∂, B_jet, B_Z) by (28) → mParam, bDel, bJet, bZ ρ a n (definition Params); reason: the printed formulas of (28), as functions of (ρ, a, n) only
--   - encoding: field of characteristic zero or p > max{k − 1, B∂} → ringChar F = 0 ∨ max (k − 1) B∂ < ringChar F; reason: ringChar is the characteristic; same fields
--   - encoding: positions 1, …, n; distinct evaluation points α_1, …, α_n → Fin n (0-based); α : Fin n → F with Function.Injective α; reason: Lean indexing; the same instances
--   - encoding: every field F → every F : Type u (one universe, quantified inside the statement); reason: Lean universes; every field is isomorphic to one in the universe of its elements
--   - encoding: for every received line there is one exceptional set E … → HasLineMCA k α A (41) (Definition 3.2; E : Finset F chosen per line before z and P); reason: Definition 3.2 is exactly this property
--   - reading: Over F_q, divide the (exceptional) count by q for the soundness error → not a separate clause; reason: it interprets the count: |E|/q is the probability that a uniform challenge in F_q lies in E, immediate from the count bound
-- source:
--   Dao, Kominers, Thaler, Reed–Solomon Codes Beyond Johnson: Efficient Decoding and Smaller Cryptographic Proofs, STOC 2027 submission (manuscript of November 2, 2026, sha256 76a38731…), pp. 30–31, Theorem 5.2

import Mathlib
import Definitions.Def_RSBeyondJohnson_FirstOrder_Agreement
import Definitions.Def_RSBeyondJohnson_FirstOrder_Curve
import Definitions.Def_RSBeyondJohnson_FirstOrder_Params
import Definitions.Def_RSBeyondJohnson_FirstOrder_Counting

open Polynomial

namespace RSBeyondJohnson.FirstOrder

/-- **Theorem 5.2 (First-order line MCA above the first-order curve)**, pp. 30–31. For every
rate `0 < ρ < 1` there is `C_ρ > 0` such that: for `ρ < a < 1` with `a > a₁(ρ)`, integers
`n ≥ 2`, `2 ≤ k ≤ ρn`, `an ≤ A ≤ n`, `(m, B∂, B_jet, B_Z)` from (28), `D = k − 1`,
`λ_agr = (n − D)/(A − D)`, `b = B_jet(2B∂ + 1)`, `h = B_Z(2B∂ + 1)`, the explicit bound (41)
`(2b − 1)h + λ_agr(h + b + 4Dbh) + (n − D − 1)b + (48D²B_Z + 16D)λ_agr² B_jet B∂
+ 8D(n − D − 1)λ_agr B_jet B∂` is at most `C_ρ n²/(η₁ + 1/n)⁴` and at most `C_ρ n²/η₁⁴`
(`η₁ = a − a₁(ρ)`), and over every field of characteristic zero or `p > max{k − 1, B∂}` and all
distinct evaluation points, `RS_α[n, k]` has line MCA with full agreement sets at threshold `A`
with exceptional bound (41) (Definition 3.2: one exceptional set per received line). -/
theorem theorem_5_2.{u} :
    ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∃ C : ℝ, 0 < C ∧
      ∀ (a : ℝ) (n k A : ℕ), ρ < a → a < 1 → a1 ρ < a → 2 ≤ n → 2 ≤ k → (k : ℝ) ≤ ρ * n →
        a * n ≤ (A : ℝ) → A ≤ n →
        ((2 * ((bJet ρ a n : ℝ) * (2 * bDel ρ a n + 1)) - 1) * ((bZ ρ a n : ℝ) * (2 * bDel ρ a n + 1)) +
            lamAgr n (k - 1) A * ((bZ ρ a n : ℝ) * (2 * bDel ρ a n + 1) +
              (bJet ρ a n : ℝ) * (2 * bDel ρ a n + 1) +
              4 * ((k : ℝ) - 1) * ((bJet ρ a n : ℝ) * (2 * bDel ρ a n + 1)) *
                ((bZ ρ a n : ℝ) * (2 * bDel ρ a n + 1))) +
            ((n : ℝ) - ((k : ℝ) - 1) - 1) * ((bJet ρ a n : ℝ) * (2 * bDel ρ a n + 1)) +
            (48 * ((k : ℝ) - 1) ^ 2 * bZ ρ a n + 16 * ((k : ℝ) - 1)) * lamAgr n (k - 1) A ^ 2 *
              bJet ρ a n * bDel ρ a n +
            8 * ((k : ℝ) - 1) * ((n : ℝ) - ((k : ℝ) - 1) - 1) * lamAgr n (k - 1) A *
              bJet ρ a n * bDel ρ a n ≤
          C * (n : ℝ) ^ 2 / (a - a1 ρ + 1 / (n : ℝ)) ^ 4) ∧
        ((2 * ((bJet ρ a n : ℝ) * (2 * bDel ρ a n + 1)) - 1) * ((bZ ρ a n : ℝ) * (2 * bDel ρ a n + 1)) +
            lamAgr n (k - 1) A * ((bZ ρ a n : ℝ) * (2 * bDel ρ a n + 1) +
              (bJet ρ a n : ℝ) * (2 * bDel ρ a n + 1) +
              4 * ((k : ℝ) - 1) * ((bJet ρ a n : ℝ) * (2 * bDel ρ a n + 1)) *
                ((bZ ρ a n : ℝ) * (2 * bDel ρ a n + 1))) +
            ((n : ℝ) - ((k : ℝ) - 1) - 1) * ((bJet ρ a n : ℝ) * (2 * bDel ρ a n + 1)) +
            (48 * ((k : ℝ) - 1) ^ 2 * bZ ρ a n + 16 * ((k : ℝ) - 1)) * lamAgr n (k - 1) A ^ 2 *
              bJet ρ a n * bDel ρ a n +
            8 * ((k : ℝ) - 1) * ((n : ℝ) - ((k : ℝ) - 1) - 1) * lamAgr n (k - 1) A *
              bJet ρ a n * bDel ρ a n ≤
          C * (n : ℝ) ^ 2 / (a - a1 ρ) ^ 4) ∧
        ∀ (F : Type u) [Field F], (ringChar F = 0 ∨ max (k - 1) (bDel ρ a n) < ringChar F) →
          ∀ α : Fin n → F, Function.Injective α →
            HasLineMCA k α A
              ((2 * ((bJet ρ a n : ℝ) * (2 * bDel ρ a n + 1)) - 1) *
                  ((bZ ρ a n : ℝ) * (2 * bDel ρ a n + 1)) +
                lamAgr n (k - 1) A * ((bZ ρ a n : ℝ) * (2 * bDel ρ a n + 1) +
                  (bJet ρ a n : ℝ) * (2 * bDel ρ a n + 1) +
                  4 * ((k : ℝ) - 1) * ((bJet ρ a n : ℝ) * (2 * bDel ρ a n + 1)) *
                    ((bZ ρ a n : ℝ) * (2 * bDel ρ a n + 1))) +
                ((n : ℝ) - ((k : ℝ) - 1) - 1) * ((bJet ρ a n : ℝ) * (2 * bDel ρ a n + 1)) +
                (48 * ((k : ℝ) - 1) ^ 2 * bZ ρ a n + 16 * ((k : ℝ) - 1)) *
                  lamAgr n (k - 1) A ^ 2 * bJet ρ a n * bDel ρ a n +
                8 * ((k : ℝ) - 1) * ((n : ℝ) - ((k : ℝ) - 1) - 1) * lamAgr n (k - 1) A *
                  bJet ρ a n * bDel ρ a n) := by sorry

end RSBeyondJohnson.FirstOrder
