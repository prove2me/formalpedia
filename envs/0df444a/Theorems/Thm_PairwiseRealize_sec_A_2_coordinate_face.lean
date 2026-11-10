-- Prove2me | Theorems.Thm_PairwiseRealize_sec_A_2_coordinate_face
-- name    : PairwiseRealize.sec_A_2_coordinate_face
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T10:55:36.103376+00:00
-- url     : https://prove2.me/theorems/eec12a37-e272-42e2-84bb-d9f0ee923a27
-- title:
--   §A.2, p.12 — the coordinate face: the diagonals differ only on the pair $\{i,j\}$, by $\pm1$
-- statement:
--   For coordinates $i<j$ and a row $x$, the face $\{x,x\oplus e_i,x\oplus e_j,x\oplus e_i\oplus e_j\}$ has the diagonals $\{x,x\oplus e_i\oplus e_j\}$ and $\{x\oplus e_i,x\oplus e_j\}$. The difference of their statistics vanishes on the total, on every singleton and on every pair other than $\{i,j\}$, and is $+1$ or $-1$ on the pair $\{i,j\}$.
--
--   Leaves of the repair hierarchy use these faces to remove the last integer error.
--
--   Differences from the source:
--   - encoding: a coordinate face for i, j → the unordered pair written i < j; reason: coordinates are unordered pairs in this mission
-- source:
--   Shi, Sun, Robust Exact Realization of Pairwise Boolean Statistics, STOC 2027 submission (sha256 62090516…), §A.2, p.12 (PDF p.13)

import Mathlib
import Definitions.Def_PairwiseRealize_Model

namespace PairwiseRealize

/-- **The coordinate face, §A.2 p.12 (PDF p.13).** K. Shi, H. Sun, *Robust Exact Realization of
Pairwise Boolean Statistics*, STOC 2027 submission (manuscript sha256 62090516…): "At a leaf use 2T_R
coordinate faces avoiding D, with T_R baseline orientations of each sign. On a coordinate face for
i, j, the two diagonals have equal total and singleton counts and pair-ij difference +1 or −1; every
other pair cancels."

For coordinates `i < j` and a row `x`, the face `{x, x⊕eᵢ, x⊕eⱼ, x⊕eᵢ⊕eⱼ}` has the diagonals
`{x, x⊕eᵢ⊕eⱼ}` and `{x⊕eᵢ, x⊕eⱼ}`; the difference of their statistics vanishes on the total, on every
singleton and on every pair other than `{i, j}`, and is `+1` or `−1` on the pair `{i, j}`.

**Formalization Note** The unordered pair `{i, j}` is written with `i < j`. -/
theorem sec_A_2_coordinate_face (n : ℕ) (i j : Fin n) (hij : i < j) (x : Row n) :
    let flip : Row n → Fin n → Row n := fun y k => Function.update y k (!y k)
    let Δ : Feat n → ℤ := fun f =>
      wvec n x f + wvec n (flip (flip x i) j) f - wvec n (flip x i) f - wvec n (flip x j) f
    Δ Feat.total = 0 ∧ (∀ k, Δ (Feat.single k) = 0) ∧
      (Δ (Feat.pair i j hij) = 1 ∨ Δ (Feat.pair i j hij) = -1) ∧
      ∀ k l (h : k < l), (k, l) ≠ (i, j) → Δ (Feat.pair k l h) = 0 := by sorry

end PairwiseRealize
