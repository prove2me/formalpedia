-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P31_fine_projector_irrep_action
-- name    : QAlgorithms.Papers.Independent.Extend50.P31.fine_projector_irrep_action
-- status  : Proved
-- author  : @Mrnaiq
-- created : 2026-11-14T05:37:06.690448+00:00
-- url     : https://prove2.me/theorems/73f2f90c-4e47-4f96-88ea-919ee663b56a
-- title:
--   Fine matrix-coefficient projectors select one coordinate of one irreducible block
-- statement:
--   Let $G$ be a finite group and $(\varphi^a)$ a coordinate-fixed family of pairwise inequivalent unitary irreducible complex representations with dimensions $d_a>0$. For a label $a$ and coordinate $i<d_a$, define the matrix-coefficient weighted average acting on a block $b$ by
--
--   $$Q_{a,i}^{(b)}=\frac{d_a}{|G|}\sum_{g\in G}\varphi^a(g^{-1})_{ii}\varphi^b(g).$$
--
--   If $a\ne b$, this matrix is zero. If $a=b$, it is the matrix unit $E_{ii}$ in the fixed coordinate basis. In the formal statement the coordinate is transported across the equality of labels. This is the fine-projector case of Schur matrix-coefficient orthogonality, and no finiteness of the label type is required.
-- source:
--   Mozrzymas, Studzinski and Datta, Structure of irreducibly covariant quantum channels for finite groups, https://arxiv.org/abs/1610.05657v2, PDF p.10 Schur matrix-coefficient orthogonality Eq.(43), and Proposition 17 fine-projector construction Eqs.(57)–(60), PDF p.12.

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P31
noncomputable section
open QAlgorithms.Papers.Independent.Extend50.P31 QAlgorithms.Papers.Independent.Information100.P44
open scoped Matrix ComplexConjugate

theorem QAlgorithms.Papers.Independent.Extend50.P31.fine_projector_irrep_action {G A : Type*} [Group G] [Fintype G] [DecidableEq A] (F : IrrepFamily G A) (a b : A) (i : Fin (F.dim a)) :
    ((F.dim a : ℂ) / Fintype.card G) •
      (∑ g : G, (F.irrep a).rho g⁻¹ i i • (F.irrep b).rho g) =
      if h : a = b then Matrix.single (Fin.cast (congrArg F.dim h) i)
        (Fin.cast (congrArg F.dim h) i) 1 else 0 := by sorry
