-- Prove2me | Theorems.Thm_PolyEvalDS_LargeChar_Supplement_corollary_5_8
-- name    : PolyEvalDS.LargeChar.Supplement.corollary_5_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:58:15.764438+00:00
-- url     : https://prove2.me/theorems/e9f0d6c2-fe9c-49c0-b2ee-db35a00d76e1
-- title:
--   Corollary 5.8 — a monic $h\in\mathbb Z[X]$ with $h(b)\equiv0$ dividing every small $\{-1,0,1\}$-polynomial vanishing at $b$
-- statement:
--   Let $d\ge0$ be an integer and let $p$ be a prime with
--
--   $$
--   p>(d+1)^{3d/2},
--   $$
--
--   and let $b\in\mathbb F_p$ be arbitrary. Then there is a **monic** polynomial $h\in\mathbb Z[X]$ such that
--
--   1. $h(b)\equiv0\pmod p$, and
--   2. $h$ divides, in $\mathbb Z[X]$, every polynomial $g\in\mathbb Z[X]$ of degree at most $d$ with every coefficient in $\{-1,0,1\}$ and $g(b)\equiv 0\pmod p$.
--
--   Divisibility is over the integers, not merely modulo $p$. The element $b$ may be $0$.
--
--   This corollary is the first step of the proof of Theorem 5.5: it converts a coincidence of two $0/1$ power sums at $b$ modulo $p$ into a divisibility by the fixed integer polynomial $h$.
--
--   **Formalization Note** The reduction modulo $p$ is `Polynomial.map (Int.castRingHom (ZMod p))` followed by evaluation at `b : ZMod p`; divisibility is `∣` in `ℤ[X]`.
--
--   Differences from the source:
--   - generalization: d the degree bound of §5, a positive integer → d : ℕ, so d = 0 is included; reason: the statement at d = 0 is the same claim for constant polynomials and is true; for d ≥ 1 the Lean statement is exactly the source's
--   - encoding: b ∈ F_p, p a prime → p : ℕ with hp : p.Prime and b : ZMod p; reason: ZMod p is the field F_p for p prime
--   - encoding: q(b) ≡ 0 mod p for q ∈ ℤ[X] and b ∈ F_p → (q.map (Int.castRingHom (ZMod p))).eval b = 0; reason: reducing the coefficients mod p and evaluating at b in ZMod p is the meaning of the congruence
--   - encoding: (d+1)^{3d/2} → ((d:ℝ)+1) ^ ((3*(d:ℝ))/2), a real power; reason: 3d/2 is not an integer for odd d; the real power is the printed value
--   - encoding: all polynomials g ∈ ℤ[X] of degree at most d with coefficients in {−1, 0, 1} → ∀ g : ℤ[X], g.natDegree ≤ d → (∀ i, g.coeff i ∈ {−1, 0, 1}) → …; reason: same set of polynomials; g = 0 is included, as in the source
-- source:
--   Hiroki Okada, Rachel Player, Simon Pohmann, An Algebraic Polynomial Evaluation Datastructure for Fields of Large Characteristic, STOC 2027 submission #463 (October 2026), source.pdf SHA-256 33e2ace7597795eb2f5be3a68d2beb3fd8c69139336faf4559faf1452360646b, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/463.pdf, Corollary 5.8, p. 12

import Mathlib
open Polynomial

namespace PolyEvalDS.LargeChar.Supplement

/-- Corollary 5.8, p. 12 (Okada, Player, Pohmann, STOC 2027 submission #463, October 2026).
If `p > (d + 1)^(3d/2)` is a prime and `b ∈ F_p`, then there is a monic `h ∈ ℤ[X]` with
`h(b) ≡ 0 mod p` which divides, in `ℤ[X]`, every `g ∈ ℤ[X]` of degree at most `d` with
coefficients in `{-1, 0, 1}` and `g(b) ≡ 0 mod p`.
Reduction mod `p` is `Polynomial.map (Int.castRingHom (ZMod p))`; divisibility is in `ℤ[X]`. -/
theorem corollary_5_8 (p d : ℕ) (hp : p.Prime)
    (hpd : ((d : ℝ) + 1) ^ ((3 * (d : ℝ)) / 2) < (p : ℝ)) (b : ZMod p) :
    ∃ h : ℤ[X], h.Monic ∧ (h.map (Int.castRingHom (ZMod p))).eval b = 0 ∧
      ∀ g : ℤ[X], g.natDegree ≤ d → (∀ i, g.coeff i ∈ ({-1, 0, 1} : Set ℤ)) →
        (g.map (Int.castRingHom (ZMod p))).eval b = 0 → h ∣ g := by sorry

end PolyEvalDS.LargeChar.Supplement
