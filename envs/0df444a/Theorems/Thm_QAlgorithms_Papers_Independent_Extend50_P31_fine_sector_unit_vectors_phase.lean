-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P31_fine_sector_unit_vectors_phase
-- name    : QAlgorithms.Papers.Independent.Extend50.P31.fine_sector_unit_vectors_phase
-- status  : Open
-- author  : @Mrnaiq
-- created : 2026-11-14T05:58:47.97381+00:00
-- url     : https://prove2.me/theorems/0d009f33-685a-4d64-802f-cb213a40f380
-- title:
--   Any two unit eigenmatrices in one fine sector differ by a global phase
-- statement:
--   Under the finite-group irreducible and multiplicity-free decomposition assumptions, fix a fine sector $r$. If two matrices $X,Y\in M_n(\mathbb C)$ have unit Hilbert–Schmidt norm and are fixed by its fine projector, then
--
--   $$Y=e^{it}X\quad\text{for some }t\in\mathbb R.$$
--
--   The statement applies to any unit matrices in that sector, including all positive-pivot normalized eigenmatrices. It makes their phase ambiguity explicit and requires no relation between the pivots or their coordinates.
-- source:
--   Mozrzymas, Studzinski and Datta, Structure of irreducibly covariant quantum channels for finite groups, https://arxiv.org/abs/1610.05657v2, PDF pp.13–14, Proposition 20 Eqs.(61)–(63) and Corollary 21 Eq.(64); unit-vector formulation of the one-dimensional fine-sector phase ambiguity.

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P31
noncomputable section
open QAlgorithms.Papers.Independent.Extend50.P31
open QAlgorithms.Papers.Independent.Information100.P44 (Mat matrixUnit)
open QAlgorithms.Papers.Independent.Frontier18.P17 (hs res)
open QAlgorithms.Papers.Independent.Information100.P75 (phase)

theorem QAlgorithms.Papers.Independent.Extend50.P31.fine_sector_unit_vectors_phase {G A : Type*} [Group G] [Fintype G] [Fintype A] [DecidableEq A] {n : ℕ} (D : Data G A n) (r : Row D) (X Y : Mat n)
    (hx : hs X X = 1) (hy : hs Y Y = 1)
    (hfx : fineMap D.U D.F r.1.val r.2 X = X)
    (hfy : fineMap D.U D.F r.1.val r.2 Y = Y) : ∃ t : ℝ, Y = phase t • X := by sorry
