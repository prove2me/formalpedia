-- Prove2me | Theorems.Thm_PolySwap_KMS_proposition_5_14
-- name    : PolySwap.KMS.proposition_5_14
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:42:01.59422+00:00
-- url     : https://prove2.me/theorems/7b623a91-b1cd-4933-94a9-f4acb7e037b3
-- title:
--   Proposition 5.14 — every $g\in\mathrm{Unip}_n(R)$ is a product of at most 6 elements of $H_1\cup H_2$
-- statement:
--   Let $R$ be a commutative unital ring, $n\ge5$, and let $H_1,H_2<\mathrm{Unip}_n(R)$ be
--   $$H_1=\langle E_{i,j}(A):1\le i\le j\le4,\ A\ (i,j)\text{-admissible}\rangle,\qquad H_2=\langle E_{i,5}(A):2\le i\le5,\ A\ (i,5)\text{-admissible}\rangle.$$
--   Then every element $g\in\mathrm{Unip}_n(R)$ can be written as a product of at most 6 elements of $H_1\cup H_2$.
--
--   Differences from the source:
--   - reading: H₂ = ⟨E_{i,5}(A) : 2 ≤ i ≤ 5, A is (i, j)-admissible⟩ → A is (i, 5)-admissible; reason: the only j in the generator E_{i,5}(A) is 5
--   - encoding: (i, j)-admissible block matrices and E_{i,j}(A); the subgroups H₁, H₂ → the embedded n × n encoding of the Unip definition; H₁, H₂ as hypotheses hH₁, hH₂ fixing them to the subgroup closures; reason: same groups
--   - encoding: n ≥ 5 (standing for the 5-block form, p. 37) → hypothesis 5 ≤ n; reason: the section's standing assumption
-- source:
--   Dikstein, Oppenheim, Valentiner-Branth, Polynomial Swap Coboundary Expansion with Applications to LTCs and PCPs, STOC 2027 submission (manuscript sha256 b9cb2095…), Proposition 5.14, p. 46

import Mathlib
import Definitions.Def_PolySwap_KMS_Unip

namespace PolySwap.KMS

/-- **Proposition 5.14**, p. 46. Let `n ≥ 5` and let `H₁, H₂ < Unip_n(R)` be
`H₁ = ⟨E_{i,j}(A) : 1 ≤ i ≤ j ≤ 4, A (i, j)-admissible⟩` and
`H₂ = ⟨E_{i,5}(A) : 2 ≤ i ≤ 5, A (i, 5)-admissible⟩`. Then every `g ∈ Unip_n(R)` is a product
of at most 6 elements of `H₁ ∪ H₂`. -/
theorem proposition_5_14 (n : ℕ) (R : Type*) [CommRing R] (hn : 5 ≤ n)
    (H₁ H₂ : Subgroup (Unip n R))
    (hH₁ : H₁ = Subgroup.closure {g | ∃ i j A, 1 ≤ i ∧ i ≤ j ∧ j ≤ 4 ∧ Admissible n R i j A ∧
      umat n R g = E n R i j A})
    (hH₂ : H₂ = Subgroup.closure {g | ∃ i A, 2 ≤ i ∧ i ≤ 5 ∧ Admissible n R i 5 A ∧
      umat n R g = E n R i 5 A}) :
    ∀ g : Unip n R, ∃ l : List (Unip n R), l.length ≤ 6 ∧ (∀ x ∈ l, x ∈ H₁ ∨ x ∈ H₂) ∧
      l.prod = g := by sorry

end PolySwap.KMS
