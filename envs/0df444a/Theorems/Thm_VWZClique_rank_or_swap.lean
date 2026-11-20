-- Prove2me | Theorems.Thm_VWZClique_rank_or_swap
-- name    : VWZClique.rank_or_swap
-- status  : Proved
-- author  : @orz
-- created : 2026-11-20T01:03:08.34786+00:00
-- url     : https://prove2.me/theorems/bd29543c-4c79-4e54-a035-3be43851b321
-- title:
--   Lemma 3.3 — Rank-or-swap identity and size bounds
-- statement:
--   For every positive term-count exponent, the identity on ordered bit-string pairs splits into few partial swaps and few rank-one terms in the explicit product basis. The identity uses integer swap coefficients and rational spectral weights. This milestone covers the algebraic identity and the two cardinality bounds.
-- source:
--   V. Vassilevska Williams and O. Zamir, The k-Clique hypothesis is dead, for good (2026), Lemma 3.3, Section 4 and Appendix A. https://zamir.prof/kclq.pdf

import Definitions.Def_VWZClique_Operators

open VWZClique

theorem VWZClique.rank_or_swap :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∃ L₀ : ℕ, ∀ L ≥ L₀,
      ∃ (M : ℕ) (m : Fin M → Mask L) (c : Fin M → ℤ)
        (Λ : Finset (BasisLabel L)) (d : BasisLabel L → ℚ),
        (M : ℝ) ≤ ((2:ℝ)^L)^ε ∧ (Λ.card : ℝ) ≤ ((2:ℝ)^L)^(2-δ) ∧
        ∀ x y : PairBits L,
          (if x = y then (1 : ℚ) else 0) =
            (∑ j ∈ Λ, d j * basisEntry j x * basisEntry j y) +
            ∑ i, (c i : ℚ) * swapEntry (m i) x y := by sorry
