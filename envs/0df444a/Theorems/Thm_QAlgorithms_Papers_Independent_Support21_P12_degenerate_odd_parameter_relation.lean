-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P12_degenerate_odd_parameter_relation
-- name    : QAlgorithms.Papers.Independent.Support21.P12.degenerate_odd_parameter_relation
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T04:14:24.777812+00:00
-- url     : https://prove2.me/theorems/95c92504-179e-4062-9e5f-344bd700774e
-- title:
--   Odd-parameter identity and its characteristic-two consequence
-- statement:
--   Let $S$ be a commutative unital ring and let $\widehat N_{2,S}$ be the actual degenerate affine BMW algebra with sequence $\Omega$. Suppose the scalar map $s\mapsto se_1$ is injective. For every $a\ge0$,
--
--   $$2\omega_{2a+1}=-\omega_{2a}+\sum_{b=1}^{2a+1}(-1)^{b-1}\omega_{b-1}\omega_{2a+1-b}.$$
--
--   If S has characteristic two, then $\omega_{2a}=\omega_a^2$ for every $a\ge0$. At $a=0$ the first identity reads $2\omega_1=-\omega_0+\omega_0^2$. The characteristic-two consequence constrains the sequence without any cyclotomic assumption.
-- source:
--   Remarks on Cyclotomic and Degenerate Cyclotomic BMW Algebras, arXiv:1011.3284v3, PDF p. 18, Lemma 7.2

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P12

noncomputable section

open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Support21.P12

universe u

/-- Lemma 7.2, BOTH parts, PDF p.18. At a=0 the first equation is
2 omega_1 = -omega_0 + omega_0^2. The second part requires characteristic 2. -/
theorem degenerate_odd_parameter_relation (S : Type*) [CommRing S] (omega : ℕ → S)
    (he : Function.Injective fun s : S => s • ae S omega .degenerate 2 0) :
    (∀ a : ℕ, 2 * omega (2*a+1) = -omega (2*a) +
      ∑ b ∈ Finset.Icc 1 (2*a+1), (-1 : S) ^ (b-1) * omega (b-1) * omega (2*a+1-b)) ∧
    (CharP S 2 → ∀ a : ℕ, omega (2*a) = omega a ^ 2) := by sorry

end QAlgorithms.Papers.Independent.Support21.P12

end
