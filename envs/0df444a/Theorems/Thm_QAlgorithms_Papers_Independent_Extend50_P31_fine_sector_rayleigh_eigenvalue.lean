-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P31_fine_sector_rayleigh_eigenvalue
-- name    : QAlgorithms.Papers.Independent.Extend50.P31.fine_sector_rayleigh_eigenvalue
-- status  : Proved
-- author  : @Mrnaiq
-- created : 2026-11-14T06:27:51.743257+00:00
-- url     : https://prove2.me/theorems/1e4564ad-a424-401c-8d07-90c259276647
-- title:
--   A matrix commuting with a fine projector has its unit vector as a Rayleigh eigenvector
-- statement:
--   Under the finite-group irreducible and multiplicity-free decomposition assumptions, fix a fine sector $r$ with projector $Q_r$. Let $M$ be any complex matrix commuting with $Q_r$, and let $w$ be a unit vector fixed by $Q_r$. Then
--
--   $$Mw=\langle w,Mw\rangle w.$$
--
--   No Hermiticity or positivity of $M$ is assumed. The chosen vector need not come from any particular pivot. The Rayleigh scalar is its genuine eigenvalue because the fine projector has one-dimensional range; the result is used to diagonalize Choi matrices in the fine eigenbasis.
-- source:
--   Mozrzymas, Studzinski and Datta, Structure of irreducibly covariant quantum channels for finite groups, https://arxiv.org/abs/1610.05657v2, PDF pp.12–15, fine rank-one projectors Eq.(56), unit eigenmatrices Eqs.(61)–(63), and simultaneous Choi eigenvalues in Proposition 30 Eqs.(75)–(77).

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P31
noncomputable section
open QAlgorithms.Papers.Independent.Extend50.P31
open scoped Matrix ComplexConjugate

theorem QAlgorithms.Papers.Independent.Extend50.P31.fine_sector_rayleigh_eigenvalue {G A : Type*} [Group G] [Fintype G] [Fintype A] [DecidableEq A] {n : ℕ} (D : Data G A n) (r : Row D)
    (M : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) (w : (Fin n × Fin n) → ℂ)
    (hfix : (fineMatrix D.U D.F r.1.val r.2).mulVec w = w)
    (hnorm : (∑ p, conj (w p) * w p) = 1)
    (hcomm : M * fineMatrix D.U D.F r.1.val r.2 = fineMatrix D.U D.F r.1.val r.2 * M) :
    M.mulVec w = (∑ p, conj (w p) * M.mulVec w p) • w := by sorry
