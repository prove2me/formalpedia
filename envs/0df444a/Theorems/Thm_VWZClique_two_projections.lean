-- Prove2me | Theorems.Thm_VWZClique_two_projections
-- name    : VWZClique.two_projections
-- status  : Proved
-- author  : @orz
-- created : 2026-11-20T01:04:08.981053+00:00
-- url     : https://prove2.me/theorems/bb974b67-e1ed-47d6-8823-b51b1ed8565a
-- title:
--   Lemma 3.4 — Cost of the doubly projected contraction
-- statement:
--   For two fixed subsets of product-basis labels with at most $n^{2-\delta}$ elements each, the entire contraction over factorized channels has arithmetic cost $n^{3\omega_F-(\omega_F-1)\delta+o(1)}$. The program receives the unary and pairwise tables.
-- source:
--   V. Vassilevska Williams and O. Zamir, The k-Clique hypothesis is dead, for good (2026), Lemma 3.4. https://zamir.prof/kclq.pdf

import Definitions.Def_VWZClique_Contraction

open VWZClique OAI.MatrixMultiplication.Arithmetic

theorem VWZClique.two_projections :
    ∀ (F : Type*) [Field F] [CharZero F] (δ : ℝ), 0 < δ → δ ≤ 1 →
      ∀ η : ℝ, 0 < η → ∃ C : ℝ, 0 < C ∧ ∀ (L : ℕ)
        (Λ Γ : Finset (BasisLabel L)) (d e : BasisLabel L → F),
        (Λ.card : ℝ) ≤ ((2 : ℝ)^L)^(2-δ) →
        (Γ.card : ℝ) ≤ ((2 : ℝ)^L)^(2-δ) →
        computesWithin (doubleProjection Λ Γ d e)
          (C * ((2 : ℝ)^L)^(3 * omega F - (omega F - 1)*δ + η)) := by sorry
