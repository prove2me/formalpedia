-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P83_finiteChargeReservoir
-- name    : QAlgorithms.Papers.Independent.Intake100.P83.finiteChargeReservoir
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:13:24.294259+00:00
-- url     : https://prove2.me/theorems/6a40cc5d-5abc-4ef0-ad0c-51ca9663ed70
-- title:
--   A finite charge reservoir gives semi-universality
-- statement:
--   Let $G$ be an Abelian group and let $A$ be a finite nonempty orthonormal on-site basis, with $d=|A|$. For each $a\in A$, let $\chi_a:G\to\mathbb C$ be a unit-modulus character, so that $u(g)=\operatorname{diag}(\chi_a(g))$ and the physical action on $n$ sites is $U_n(g)=u(g)^{\otimes n}$. Write $\mathcal V_{n,k}$ for the exact finite products of individually $G$-invariant unitaries acting on at most $k$ arbitrary named sites. A product string $r\in A^n$ has character $\chi_r=\prod_j\chi_{r_j}$; a charge sector is the full span of all strings with the same character.
--
--   Assume $G$ finite and $n\ge1$. Let $q_l$ be the number of characters occurring on $l$ sites and define the actual reservoir size
--
--   $$
--   l_* = \min\{l\ge1:q_l=q_n\}.
--   $$
--
--   Then $1\le l_*\le n$, $q_{l_*}=q_n\le|G|$, and, if $q_1>1$, then $l_*\le|G|-1$. For every $l_*+1\le k\le n$, the gates are semi-universal, their complex commutant equals that of all symmetric unitaries and has dimension $q_n$, and equal-charge basis strings admit the paths of Theorem 2′.
--
--   The reservoir size is computed from the given on-site representation, providing the finite-group bound without an unconstrained auxiliary parameter.
-- source:
--   Theory of Quantum Circuits with Abelian Symmetries, arXiv:2302.12466v3, PDF p. 7, IV B, unnumbered: finite charge reservoir gives semi-universality

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P83

noncomputable section

open scoped BigOperators ComplexConjugate Matrix Kronecker Manifold ContDiff

attribute [local instance] Classical.propDecidable

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

namespace QAlgorithms.Papers.Independent.Intake100.P83

variable {A G : Type*} [Fintype A] [DecidableEq A]

/-- PDF p.7 Eqs.(13)-(14): the reservoir length is the actual least positive charge-count match.
The |G|-1 bound is conditional on more than one on-site character. -/
theorem finiteChargeReservoir [CommGroup G] [Fintype G] [Nonempty A]
    (chi : A → G → ℂ) (hchi : IsOnsite chi) (n : ℕ) (hn : 1 ≤ n) :
    0 < reservoirLength chi n ∧ reservoirLength chi n ≤ n ∧
    chargeCount chi (reservoirLength chi n) = chargeCount chi n ∧
    chargeCount chi n ≤ Fintype.card G ∧
    (1 < chargeCount chi 1 → reservoirLength chi n ≤ Fintype.card G - 1) ∧
    ∀ k, reservoirLength chi n + 1 ≤ k → k ≤ n →
      SemiUniversal chi n k ∧ NoExtra chi n k ∧ CommDimension chi n k ∧
      TransitiveCharges chi n k := by sorry

end QAlgorithms.Papers.Independent.Intake100.P83

end
