-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P09_symmetry_preserving_dilation
-- name    : QAlgorithms.Papers.Independent.Support21.P09.symmetry_preserving_dilation
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T03:40:51.687353+00:00
-- url     : https://prove2.me/theorems/f1ebc676-6a27-422d-bbd3-c39c42dbbebc
-- title:
--   Symmetry-preserving orthogonal dilation
-- statement:
--   Let $G$ be a finite group, let $d>0$ and $c\ge0$ be integers, and put $n=d+c$. Let $\phi:G\to U(d)$ be an ordinary representation and let $M\in\mathbb C^{d\times n}$ have nonzero columns $v_j$. Assume that the distinct effects $A_j=v_jv_j^\dagger$ sum to $I_d$ and are invariant under conjugation by $\phi(G)$. Let $J:\mathbb C^d\to\mathbb C^n$ include the first $d$ coordinates. There exist an ordinary monomial unitary representation $R$ on $\mathbb C^n$, an ordinary unitary representation $\chi$ on $\mathbb C^c$, and $B\in U(n)$ such that
--
--   $$
--   \phi(g)M=MR(g),\qquad J^\dagger B=M,\qquad (\phi(g)\oplus\chi(g))B=BR(g)\quad(g\in G).
--   $$
--
--   For every positive semidefinite matrix $\rho$ of trace one and every outcome $j$,
--
--   $$
--   [B^\dagger(J\rho J^\dagger)B]_{jj}=\operatorname{tr}(\rho A_j).
--   $$
--
--   Thus the columns of $B$ give an orthogonal dilation and $B^\dagger$ followed by computational measurement implements the original POVM. The complement may have dimension zero; efficiency is asserted only for the later special families.
-- source:
--   Implementation of group-covariant POVMs by orthogonal measurements, arXiv:quant-ph/0407054v1, PDF p. 2, Paper main result: symmetry-preserving orthogonal dilation

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P09

noncomputable section

namespace QAlgorithms.Papers.Independent.Support21.P09

open scoped BigOperators ComplexConjugate

open QAlgorithms.Papers.Independent.Frontier18.P17 (clock)

/-- PDF pp.2,7–11: the main symmetry-preserving orthogonal dilation theorem.
The complement dimension c may be zero. Algorithm 6's word "rows" is corrected to
columns, as required by the construction on p.4 and the adjoint implementation on p.5. -/
theorem symmetry_preserving_dilation
    {G : Type*} [Group G] [Fintype G] {d c : ℕ} (hd : 0 < d)
    (phi : Rep G (Fin d)) (hphi : UnitaryRep phi)
    (M : Matrix (Fin d) (Fin (d + c)) ℂ) (hM : RankOnePOVM M)
    (hdist : Function.Injective (columnEffect M)) (hcov : EffectsCovariant phi M) :
    ∃ R : Rep G (Fin (d + c)), UnitaryRep R ∧ (∀ g, Monomial (R g)) ∧
    MatrixIntertwines phi R M ∧ ∃ chi : Rep G (Fin c), UnitaryRep chi ∧
    ∃ B : Matrix (Fin (d + c)) (Fin (d + c)) ℂ,
      B ∈ Matrix.unitaryGroup (Fin (d + c)) ℂ ∧
      (∀ i j, B (Fin.castAdd c i) j = M i j) ∧
      (∀ g, sumBlock (phi g) (chi g) * B = B * R g) ∧
      ImplementsPOVM M B.conjTranspose (Fin.castAdd c) := by sorry

end QAlgorithms.Papers.Independent.Support21.P09

end
