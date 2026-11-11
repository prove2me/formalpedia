-- Prove2me | Theorems.Thm_PolynomialPackingMM_IntegerRecursion_clearing_denominators
-- name    : PolynomialPackingMM.IntegerRecursion.clearing_denominators
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:06:24.55443+00:00
-- url     : https://prove2.me/theorems/dcad06f2-7315-4bf8-955f-47f1577a044a
-- title:
--   §4.3 — denominator clearing and ordered block substitution
-- statement:
--   Let $D$ be correct finite rational matrix-multiplication identity data at side $v\ge2$. Let $d$ be the product of all coefficient denominators and $\Delta=d^3$. After scaling every encoder and decoder coefficient by $d$, the universal integer coefficient identity is the identity for $\Delta AB$. For arbitrary square integer matrix blocks $A_{ij},B_{jk}$ of every positive side,
--
--   $$\widetilde D(A,B)_{ik}=\Delta\sum_{j=1}^v A_{ij}B_{jk}.$$
--
--   This supplies the fixed denominator and ordered block substitution needed by the recursive compiler; it assumes only correctness of the scalar identity. **Formalization Note** Coefficient matching and the block equality are both conclusions. Negative block entries and noncommuting blocks are allowed.
--
--   Differences from the source:
--   - encoding: positive integer parameters and finite coefficient lists → positive naturals, zero-based finite indices and universal ordered coefficient identities; reason: the domains and every coefficient agree, and coefficient matching is valid over every characteristic-zero field
--   - encoding: a fixed positive common scale Delta after clearing the three rational maps → the product d of all positive coefficient denominators and Delta=d^3; reason: each map is scaled by d, so the two encoders and decoder together contribute precisely d^3
-- source:
--   Rafael Pass, STOC 2027 submission #1507 (October 2026), printed p. 19 (PDF 20), §4.3, proof of Theorem 1.1; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1507.pdf; SHA256 8b32ede93c8ade8e982503a0a1eec78b50621e6fcf86eba92bef2e77847b26ba

import Definitions.Def_PolynomialPackingMM_IntegerRecursion_IdentityInterface

namespace PolynomialPackingMM.IntegerRecursion

open scoped BigOperators

theorem clearing_denominators :
  ∀ D : IdentityData, 2 ≤ D.v → D.Correct →
  (∀ o a b : Fin (D.v ^ 2),
    (∑ ν : Fin D.r, D.clearCoefficient (D.leftCoeff ν a) *
      D.clearCoefficient (D.rightCoeff ν b) * D.clearCoefficient (D.outputCoeff o ν)) =
    (D.delta : ℤ) * (if o.val / D.v = a.val / D.v ∧ a.val % D.v = b.val / D.v ∧
      o.val % D.v = b.val % D.v then 1 else 0)) ∧
  (∀ (s : ℕ+) (A B : ℕ → Matrix (Fin (s : ℕ)) (Fin (s : ℕ)) ℤ)
    (i k : Fin D.v), D.blockOutput s A B (i.val * D.v + k.val) =
      (D.delta : ℤ) • ∑ j : Fin D.v, A (i.val * D.v + j.val) * B (j.val * D.v + k.val)) := by sorry

end PolynomialPackingMM.IntegerRecursion
