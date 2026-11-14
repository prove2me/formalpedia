-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P31_character_orthogonality
-- name    : QAlgorithms.Papers.Independent.Extend50.P31.character_orthogonality
-- status  : Proved
-- author  : @Mrnaiq
-- created : 2026-11-14T05:19:36.810399+00:00
-- url     : https://prove2.me/theorems/17bc494b-c22d-4b33-b8f2-97de40a25367
-- title:
--   Character orthogonality for coordinate-fixed irreducible finite-group representations
-- statement:
--   Let $G$ be a finite group and $(\varphi^a)_{a\in A}$ a coordinate-fixed family of pairwise inequivalent unitary irreducible complex representations. For any labels $a,b$, their characters satisfy
--
--   $$\frac1{|G|}\sum_{g\in G}\chi_a(g)\chi_b(g^{-1})=\begin{cases}1&a=b,\\0&a\ne b.\end{cases}$$
--
--   This is Schur character orthogonality in the paper's conventions. It applies without requiring $A$ to be finite and is the basic input for character projectors, channel trace preservation, and uniform group averaging.
-- source:
--   Mozrzymas, Studzinski and Datta, Structure of irreducibly covariant quantum channels for finite groups, https://arxiv.org/abs/1610.05657v2, PDF p.10, Schur orthogonality Eq.(43) summed on diagonal indices, and Eq.(44).

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P31
import Mathlib.RepresentationTheory.Character
import Mathlib.Analysis.Complex.Polynomial.Basic
noncomputable section
open scoped Matrix ComplexConjugate
open QAlgorithms.Papers.Independent.Extend50.P31

theorem QAlgorithms.Papers.Independent.Extend50.P31.character_orthogonality {G A : Type*} [Group G] [Fintype G] [DecidableEq A] (F : IrrepFamily G A) (a b : A) :
    (Fintype.card G : ℂ)⁻¹ * ∑ g : G, character (F.irrep a) g * character (F.irrep b) g⁻¹ =
      if a = b then 1 else 0 := by sorry
