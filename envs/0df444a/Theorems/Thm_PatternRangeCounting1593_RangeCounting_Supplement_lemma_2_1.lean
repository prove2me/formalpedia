-- Prove2me | Theorems.Thm_PatternRangeCounting1593_RangeCounting_Supplement_lemma_2_1
-- name    : PatternRangeCounting1593.RangeCounting.Supplement.lemma_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T12:04:45.945519+00:00
-- url     : https://prove2.me/theorems/205da3ba-0510-4046-b1cb-ed6f94304d96
-- title:
--   Lemma 2.1 — two-dimensional telescoping
-- statement:
--   Let $M$ be any binary $r\times c$ matrix and let $D$ be its two-dimensional XOR difference array (Equation (2), with a zero row $0$ and a zero column $0$ as padding). Then for every $(i,j)\in[r]\times[c]$,
--   $$M[i,j]=\bigoplus_{p\le i,\ s\le j} D[p,s],$$
--   where $\oplus$ is addition modulo two and the iterated XOR runs over $p\in[i]$, $s\in[j]$.
--
--   The identity holds for every binary matrix, with no mixed-freeness assumption. It turns each matrix entry into the parity of a dominance count on the support of $D$, which is the reduction behind the matrix-access theorem.
--
--   **Formalization Note** The iterated XOR is a sum in `ZMod 2` of the $0/1$ images of the entries; indices are 0-based.
--
--   Differences from the source:
--   - encoding: (i, j) ∈ [r] × [c] and p ≤ i, s ≤ j, 1-based → i : Fin r, j : Fin c, sums over Finset.Iic i and Finset.Iic j (0-based); reason: index a is the paper's a + 1; same entries
--   - encoding: iterated XOR ⨁ of bits → sum in ZMod 2 of the 0/1 images; reason: the paper defines ⊕ as addition modulo two
-- source:
--   Sankardeep Chakraborty, STOC 2027 submission #1593 (October 2026), Lemma 2.1, printed p. 8 (PDF p. 9); Equation (2), printed p. 7 (PDF p. 8)

import Mathlib
import Definitions.Def_PatternRangeCounting1593_RangeCounting_Perm
import Definitions.Def_PatternRangeCounting1593_RangeCounting_Machine
import Definitions.Def_TwinWidthI_GridThm_Setting
import Definitions.Def_PatternRangeCounting1593_RangeCounting_Supplement_MatrixAccess
set_option autoImplicit false
open PatternRangeCounting1593.RangeCounting TwinWidthI.GridThm

namespace PatternRangeCounting1593.RangeCounting.Supplement

/-- Lemma 2.1 (Two-dimensional telescoping), printed p. 8 (PDF p. 9). For every binary
`r × c` matrix `M` and every entry `(i, j)`, `M[i, j]` is the XOR (sum in `ZMod 2`) of the
XOR difference array `D` of Equation (2) over all positions `(p, s)` with `p ≤ i`, `s ≤ j`.
Index `i : Fin r` is the paper's row `i + 1`. -/
theorem lemma_2_1 {r c : ℕ} (M : Matrix (Fin r) (Fin c) Bool) (i : Fin r) (j : Fin c) :
    (if M i j then (1 : ZMod 2) else 0) =
      ∑ p ∈ Finset.Iic i, ∑ s ∈ Finset.Iic j, (if xorDiff M p s then (1 : ZMod 2) else 0) := by sorry

end PatternRangeCounting1593.RangeCounting.Supplement
