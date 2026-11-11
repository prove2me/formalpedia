-- Prove2me | Theorems.Thm_PolynomialPackingMM_IntegerRecursion_round
-- name    : PolynomialPackingMM.IntegerRecursion.round
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:06:21.38071+00:00
-- url     : https://prove2.me/theorems/74d60fae-1b4a-4d60-9324-fb0d79b36db7
-- title:
--   Lemma 4.2 — a round
-- statement:
--   Fix $d\ge1$ and positive $L,L',u,w$ with $w\ge u$. In one common exact/modulo mode, suppose both triples $(a,b,b')=(L,L,L')$ and $(L',L,L')$ admit PPs of $w$ copies of $T^d_{a,b}[1,1,w]$ using at most $2w$ copies of $T^d_{a,b'}[1,1,u]$. Put $\Lambda=\lfloor w/u\rfloor^2$. For every positive $x$ there is a PP
--
--   $$w^3\,Q^d_{L,L}[w^2\Lambda x,w^2\Lambda x,w^2\Lambda x]\quad\text{using}\quad64w^3\,Q^d_{L',L'}[w^2x,w^2x,w^2x].$$
--
--   Exactness or validity modulo $\varepsilon$ is preserved. This is the full round with its source count and all three dimension changes. **Formalization Note** Integer division computes the floor, with positivity derived from $w\ge u\ge1$.
--
--   Differences from the source:
--   - encoding: positive integer parameters and finite coefficient lists → positive naturals, zero-based finite indices and universal ordered coefficient identities; reason: the domains and every coefficient agree, and coefficient matching is valid over every characteristic-zero field
--   - encoding: rational maps or Laurent maps whose decoded error is epsilon times a polynomial in epsilon and input entries → rational-supported Laurent coefficients in exact mode, and every decoded error coefficient at degree at most zero vanishes in approximate mode; reason: universal bilinear coefficient matching imposes precisely the source error condition without evaluating epsilon inverse at zero
--   - encoding: Lambda=floor(w/u)^2 → Lambda=(w/u)^2 using natural division with a derived positivity proof; reason: w is at least u and u is positive, so the floor and all positive matrix dimensions are unchanged
-- source:
--   Rafael Pass, STOC 2027 submission #1507 (October 2026), printed p. 17 (PDF 18), Lemma 4.2; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1507.pdf; SHA256 8b32ede93c8ade8e982503a0a1eec78b50621e6fcf86eba92bef2e77847b26ba

import Definitions.Def_PolynomialPackingMM_IntegerRecursion_PackingOperations

namespace PolynomialPackingMM.IntegerRecursion

open scoped BigOperators

theorem round :
  ∀ (mode : Mode) (d L L' u w : ℕ+) (hwu : u ≤ w),
  RoundHypothesis mode d L L' u w →
  ∀ x : ℕ+,
    let Λ : ℕ+ := ⟨((w : ℕ) / u) ^ 2,
      pow_pos (Nat.div_pos (show (u : ℕ) ≤ w from hwu) u.pos) _⟩
    HasPacking mode
      (copies ((w : ℕ) ^ 3) (product (roundShape d L L)
        (w ^ 2 * Λ * x) (w ^ 2 * Λ * x) (w ^ 2 * Λ * x)))
      (copies (64 * (w : ℕ) ^ 3) (product (roundShape d L' L')
        (w ^ 2 * x) (w ^ 2 * x) (w ^ 2 * x))) := by sorry

end PolynomialPackingMM.IntegerRecursion
