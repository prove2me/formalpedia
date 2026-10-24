-- Prove2me | Theorems.Thm_ProductMixAuction_Allocate_lemma_26
-- name    : ProductMixAuction.Allocate.lemma_26
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:37:45.44609+00:00
-- url     : https://prove2.me/theorems/ea5bfd1f-22f3-4b6b-a8f1-9308bb776f76
-- title:
--   Lemma 26, p. 34 — G⁻¹Hᵢ is e^S with i ∈ S or −e^S with i ∉ S for invertible strong-substitutes matrices
-- statement:
--   Let $G$ be an invertible real $n\times n$ matrix whose rows are strong-substitutes vectors (non-zero, with at most one $+1$ entry, at most one $-1$ entry and no other non-zero entries). Split the rows of $G$ into two groups $G_1$ and $G_2$, and let $H$ be the matrix obtained from $G$ by replacing the rows of $G_1$ with zero rows, $H=(0;G_2)$; let $H_i$ be its $i$-th column. Then for every $i\in[n]$ either
--   $$G^{-1}H_i=e^S\ \text{for some}\ S\subseteq[n]\ \text{with}\ i\in S,\qquad\text{or}\qquad G^{-1}H_i=-e^S\ \text{for some}\ S\subseteq[n]\ \text{with}\ i\notin S .$$
--
--   The lemma is the linear-algebra core of Proposition 14: it shows that the price correction caused by a shift is a $0/\pm1$ indicator vector, so the new clearing price lies in $\{p\pm\varepsilon e^S\}$.
--
--   Differences from the source:
--   - generalization: G = (G₁; G₂) with G₂ the bottom block of rows → G₂ any set R of rows of G (rows outside R zeroed in H); reason: permuting rows by a permutation matrix P gives (PG)⁻¹(PH) = G⁻¹H, so the bottom-block case is the case R = bottom rows
--   - encoding: strong-substitutes vectors in ℤⁿ → real vectors with entries in {0, ±1}, at most one +1 and at most one −1, non-zero; reason: the same set of vectors
-- source:
--   Baldwin, Goldberg, Klemperer, Lock, Solving Strong-Substitutes Product-Mix Auctions, arXiv:1909.07313v3, p. 34, Lemma 26

import Mathlib
import Definitions.Def_ProductMixAuction_Allocate_Setting

namespace ProductMixAuction.Allocate

theorem lemma_26 {n : ℕ} (G : Matrix (Fin n) (Fin n) ℝ) (hG : ∀ r, IsSSVector (G r))
    (hdet : G.det ≠ 0) (R : Finset (Fin n)) :
    let H : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun r c => if r ∈ R then G r c else 0
    ∀ i : Fin n,
      (∃ S : Finset (Fin n), i ∈ S ∧
        (G⁻¹).mulVec (fun r => H r i) = fun k => if k ∈ S then 1 else 0) ∨
      (∃ S : Finset (Fin n), i ∉ S ∧
        (G⁻¹).mulVec (fun r => H r i) = fun k => if k ∈ S then -1 else 0) := by sorry

end ProductMixAuction.Allocate
