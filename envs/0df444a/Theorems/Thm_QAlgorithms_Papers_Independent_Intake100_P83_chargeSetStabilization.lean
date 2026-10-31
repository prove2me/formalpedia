-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P83_chargeSetStabilization
-- name    : QAlgorithms.Papers.Independent.Intake100.P83.chargeSetStabilization
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:26:34.803587+00:00
-- url     : https://prove2.me/theorems/1c26ed9d-1880-4758-ba1c-33eef1ab27b8
-- title:
--   Character twisting, charge-set nesting and permanent stabilization
-- statement:
--   Let $G$ be an Abelian group and let $A$ be a finite nonempty orthonormal on-site basis, with $d=|A|$. For each $a\in A$, let $\chi_a:G\to\mathbb C$ be a unit-modulus character, so that $u(g)=\operatorname{diag}(\chi_a(g))$ and the physical action on $n$ sites is $U_n(g)=u(g)^{\otimes n}$. Write $\mathcal V_{n,k}$ for the exact finite products of individually $G$-invariant unitaries acting on at most $k$ arbitrary named sites. A product string $r\in A^n$ has character $\chi_r=\prod_j\chi_{r_j}$; a charge sector is the full span of all strings with the same character.
--
--   Choose an actually occurring on-site character $\chi_a$ and twist to $\chi'_b=\chi_b/\chi_a$. Let $S_l$ be the finite set of characters occurring in $(u')^{\otimes l}$, including $S_0=\{1\}$. This twist is a unitary on-site representation and preserves every group of local symmetric circuits. Moreover,
--
--   $$
--   S_l\subseteq S_{l+1},\qquad S_{l+1}=S_lS_1,\qquad
--   S_{l+1}=S_l\ \Longrightarrow\ \forall r>l,\ S_r=S_l,
--   $$
--
--   where $S_lS_1$ is the set of pointwise products of complete characters. If $G$ is compact connected Hausdorff with continuous group operations and continuous on-site action, stabilization at any $l$ forces every twisted on-site character to be trivial.
--
--   Thus the original representation may still be scalar. Nesting is asserted only after the actual character twist.
-- source:
--   Theory of Quantum Circuits with Abelian Symmetries, arXiv:2302.12466v3, PDF p. 20, Appendix A, unnumbered: character twist, nesting and stabilization

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P83

noncomputable section

open scoped BigOperators ComplexConjugate Matrix Kronecker Manifold ContDiff

attribute [local instance] Classical.propDecidable

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

namespace QAlgorithms.Papers.Independent.Intake100.P83

variable {A G : Type*} [Fintype A] [DecidableEq A]

/-- PDF p.20 Eqs.(A24)-(A25): twist by an occurring character, then nesting, multiplication
and permanent stabilization. Topology is used only for the last connected compact clause;
"trivial" there concerns the twisted representation, hence allows scalar original actions. -/
theorem chargeSetStabilization [CommGroup G] [TopologicalSpace G] [Nonempty A]
    (chi : A → G → ℂ) (hchi : IsOnsite chi) (a : A) :
    IsOnsite (divideByOnsiteCharacter chi a) ∧
    (∀ n k, symmetricLocalGroup (divideByOnsiteCharacter chi a) n k = symmetricLocalGroup chi n k) ∧
    (∀ l, charges (divideByOnsiteCharacter chi a) l ⊆ charges (divideByOnsiteCharacter chi a) (l + 1)) ∧
    (∀ l, charges (divideByOnsiteCharacter chi a) (l + 1) =
      characterProducts (charges (divideByOnsiteCharacter chi a) l) (charges (divideByOnsiteCharacter chi a) 1)) ∧
    (∀ l, charges (divideByOnsiteCharacter chi a) (l + 1) = charges (divideByOnsiteCharacter chi a) l →
      ∀ r, l < r → charges (divideByOnsiteCharacter chi a) r = charges (divideByOnsiteCharacter chi a) l) ∧
    (IsTopologicalGroup G → CompactSpace G → T2Space G → ConnectedSpace G →
      (∀ b, Continuous (chi b)) → ∀ l,
      charges (divideByOnsiteCharacter chi a) (l + 1) = charges (divideByOnsiteCharacter chi a) l →
      ∀ b g, divideByOnsiteCharacter chi a b g = 1) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P83

end
