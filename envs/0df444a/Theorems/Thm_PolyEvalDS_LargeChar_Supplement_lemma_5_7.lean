-- Prove2me | Theorems.Thm_PolyEvalDS_LargeChar_Supplement_lemma_5_7
-- name    : PolyEvalDS.LargeChar.Supplement.lemma_5_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:58:00.193415+00:00
-- url     : https://prove2.me/theorems/d180a398-c7bd-42a0-8af8-9eb81e2de9e4
-- title:
--   Lemma 5.7 — the $\mathbb Z[X]$-gcd keeps a common root $b$ modulo $p>(d+1)^{3d/2}$
-- statement:
--   Let $d\ge0$ be an integer and let $f,g\in\mathbb Z[X]$ be polynomials of degree at most $d$ with every coefficient in $\{-1,0,1\}$, where $f\ne0$. Let $h\in\mathbb Z[X]$ divide $f$. Let $p$ be a prime with
--
--   $$
--   p>(d+1)^{3d/2},
--   $$
--
--   and suppose some $b\in\mathbb F_p$ satisfies $h(b)\equiv g(b)\equiv 0 \pmod p$, that is, the reductions of $h$ and $g$ modulo $p$ both vanish at $b$. Then
--
--   $$
--   \gcd\nolimits_{\mathbb Z[X]}(h,g)(b)\equiv 0 \pmod p .
--   $$
--
--   The greatest common divisor is taken in $\mathbb Z[X]$, where it is determined up to sign; the conclusion holds for either choice.
--
--   This lemma says that taking gcds over $\mathbb Z[X]$ among such small polynomials does not lose a common root modulo a large prime. Iterating it over all small polynomials vanishing at $b$ gives Corollary 5.8.
--
--   **Formalization Note** The reduction modulo $p$ is `Polynomial.map (Int.castRingHom (ZMod p))` followed by evaluation at `b : ZMod p`. The conclusion is stated for every $c\in\mathbb Z[X]$ that is a common divisor of $h$ and $g$ and is divisible by every common divisor of $h$ and $g$, i.e. for every gcd.
--
--   Differences from the source:
--   - generalization: d the degree bound of §5, a positive integer → d : ℕ, so d = 0 is included; reason: the statement at d = 0 is the same claim for constant polynomials and is true; for d ≥ 1 the Lean statement is exactly the source's
--   - encoding: b ∈ F_p, p a prime → p : ℕ with hp : p.Prime and b : ZMod p; reason: ZMod p is the field F_p for p prime
--   - encoding: q(b) ≡ 0 mod p for q ∈ ℤ[X] and b ∈ F_p → (q.map (Int.castRingHom (ZMod p))).eval b = 0; reason: reducing the coefficients mod p and evaluating at b in ZMod p is the meaning of the congruence
--   - encoding: gcd_{ℤ[X]}(h, g)(b) ≡ 0 mod p → for every c ∈ ℤ[X] with c ∣ h, c ∣ g and every common divisor of h and g dividing c, (c.map (Int.castRingHom (ZMod p))).eval b = 0; reason: the gcd in the UFD ℤ[X] exists and is determined up to the units ±1, which do not change whether it vanishes at b; quantifying over every gcd avoids choosing a normalization
--   - encoding: (d+1)^{3d/2} → ((d:ℝ)+1) ^ ((3*(d:ℝ))/2), a real power; reason: 3d/2 is not an integer for odd d; the real power is the printed value
-- source:
--   Hiroki Okada, Rachel Player, Simon Pohmann, An Algebraic Polynomial Evaluation Datastructure for Fields of Large Characteristic, STOC 2027 submission #463 (October 2026), source.pdf SHA-256 33e2ace7597795eb2f5be3a68d2beb3fd8c69139336faf4559faf1452360646b, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/463.pdf, Lemma 5.7, p. 12 (proof p. 12)

import Mathlib
open Polynomial

namespace PolyEvalDS.LargeChar.Supplement

/-- Lemma 5.7, p. 12 (Okada, Player, Pohmann, STOC 2027 submission #463, October 2026).
Let `f, g ∈ ℤ[X]`, `f ≠ 0`, have coefficients in `{-1, 0, 1}` and degree at most `d`, and let
`h ∈ ℤ[X]` divide `f`. If `p` is a prime with `p > (d + 1)^(3d/2)` and `h(b) ≡ g(b) ≡ 0 mod p`
for some `b ∈ F_p`, then `gcd_{ℤ[X]}(h, g)(b) ≡ 0 mod p`.
Reduction mod `p` is `Polynomial.map (Int.castRingHom (ZMod p))`. The gcd in `ℤ[X]` is determined
up to sign; the conclusion is stated for every gcd `c` of `h` and `g`, i.e. every common divisor
of `h` and `g` that every common divisor of `h` and `g` divides. -/
theorem lemma_5_7 (p d : ℕ) (hp : p.Prime) (f g h : ℤ[X]) (hf0 : f ≠ 0)
    (hf_deg : f.natDegree ≤ d) (hg_deg : g.natDegree ≤ d)
    (hf_coeff : ∀ i, f.coeff i ∈ ({-1, 0, 1} : Set ℤ))
    (hg_coeff : ∀ i, g.coeff i ∈ ({-1, 0, 1} : Set ℤ))
    (hhf : h ∣ f) (b : ZMod p)
    (hhb : (h.map (Int.castRingHom (ZMod p))).eval b = 0)
    (hgb : (g.map (Int.castRingHom (ZMod p))).eval b = 0)
    (hpd : ((d : ℝ) + 1) ^ ((3 * (d : ℝ)) / 2) < (p : ℝ)) :
    ∀ c : ℤ[X], c ∣ h → c ∣ g → (∀ e : ℤ[X], e ∣ h → e ∣ g → e ∣ c) →
      (c.map (Int.castRingHom (ZMod p))).eval b = 0 := by sorry

end PolyEvalDS.LargeChar.Supplement
