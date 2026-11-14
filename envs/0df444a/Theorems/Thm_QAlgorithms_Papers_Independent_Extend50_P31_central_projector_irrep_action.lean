-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P31_central_projector_irrep_action
-- name    : QAlgorithms.Papers.Independent.Extend50.P31.central_projector_irrep_action
-- status  : Proved
-- author  : @Mrnaiq
-- created : 2026-11-14T05:29:19.355297+00:00
-- url     : https://prove2.me/theorems/defdb276-1f25-4417-a916-b3de5ad16d86
-- title:
--   Central character projectors select exactly one irreducible representation
-- statement:
--   Let $G$ be finite and $(\varphi^a)$ a coordinate-fixed family of pairwise inequivalent irreducible unitary complex representations, with dimensions $d_a>0$ and characters $\chi_a$. Then for any two labels $a,b$,
--
--   $$\frac{d_a}{|G|}\sum_{g\in G}\chi_a(g^{-1})\varphi^b(g)=\begin{cases}I_{d_b}&a=b,\\0&a\ne b.\end{cases}$$
--
--   This is the action of a central character projector on a single irreducible block. It applies without requiring the label type to be finite and underlies the spectral decomposition of finite-group covariant quantum channels.
-- source:
--   Mozrzymas, Studzinski and Datta, Structure of irreducibly covariant quantum channels for finite groups, https://arxiv.org/abs/1610.05657v2, PDF pp.10–12, Schur orthogonality Eq.(43), central projectors Eq.(49), and orthogonal decomposition Eqs.(50)–(52).

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P31
noncomputable section
open QAlgorithms.Papers.Independent.Extend50.P31 QAlgorithms.Papers.Independent.Information100.P44
open scoped Matrix ComplexConjugate

theorem QAlgorithms.Papers.Independent.Extend50.P31.central_projector_irrep_action {G A : Type*} [Group G] [Fintype G] [DecidableEq A] (F : IrrepFamily G A) (a b : A) :
    ((F.dim a : ℂ) / Fintype.card G) •
      (∑ g : G, character (F.irrep a) g⁻¹ • (F.irrep b).rho g) =
      if a = b then (1 : Mat (F.dim b)) else 0 := by sorry
