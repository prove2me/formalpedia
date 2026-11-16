-- Prove2me | Theorems.Thm_PatternRangeCounting1593_RangeCounting_Supplement_lemma_6_1
-- name    : PatternRangeCounting1593.RangeCounting.Supplement.lemma_6_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T12:06:18.27893+00:00
-- url     : https://prove2.me/theorems/65cde7d2-204f-498d-82c6-65c9baeebeab
-- title:
--   Lemma 6.1 — the grid pattern transfers
-- statement:
--   Let $k\ge1$ and let $P\subseteq[r]\times[c]$ be a set of cells, where several cells may share a row or a column. Let $\sigma_P$ be its rank permutation (row-major position $\mapsto$ column-major rank) and $\rho_k\in S_{k^2}$ the board pattern $\rho_k((p-1)k+q)=(q-1)k+p$. Then:
--
--   1. if $\sigma_P$ contains $\rho_k$, then $P$ has a $k$-grid minor (a division of rows and columns into $k$ consecutive nonempty blocks each with a cell of $P$ in every zone);
--   2. consequently, if $P$ is $k$-grid-free, then $\sigma_P$ avoids $\rho_k$.
--
--   Together with Lemma 2.2 this shows that the support of the XOR difference array of a $t$-mixed-free matrix has a rank permutation avoiding the fixed pattern $\rho_{2t}$, so the pattern-avoiding counter applies to it.
--
--   **Formalization Note** Containment and avoidance are the published `Contains`/`Avoids` of the live mission; "$P$ has a $k$-grid minor" is `HasGridMinor` of the 0/1 indicator matrix of $P$. Both sentences of the lemma are stated, as a conjunction.
--
--   Differences from the source:
--   - encoding: ρ_k defined for k ≥ 1 (Equation (13)) → hypothesis 1 ≤ k; reason: ρ_k is undefined for k = 0 in the source; the condition only excludes that undefined case
--   - encoding: σ_P ∈ S_m and ρ_k ∈ S_{k²} on 1-based positions; 'P has a k-grid minor' → Equiv.Perm (Fin m) and Equiv.Perm (Fin (k * k)) on 0-based positions; HasGridMinor (indicator P) k; reason: same permutations after the shift by one; a k-grid minor of P is one of its 0/1 indicator matrix
-- source:
--   Sankardeep Chakraborty, STOC 2027 submission #1593 (October 2026), Lemma 6.1, printed p. 22 (PDF p. 23); §6.1 and Equation (13), printed p. 21 (PDF p. 22)

import Mathlib
import Definitions.Def_PatternRangeCounting1593_RangeCounting_Perm
import Definitions.Def_PatternRangeCounting1593_RangeCounting_Machine
import Definitions.Def_TwinWidthI_GridThm_Setting
import Definitions.Def_PatternRangeCounting1593_RangeCounting_Supplement_MatrixAccess
set_option autoImplicit false
open PatternRangeCounting1593.RangeCounting TwinWidthI.GridThm

namespace PatternRangeCounting1593.RangeCounting.Supplement

/-- Lemma 6.1 (The grid pattern transfers), printed p. 22 (PDF p. 23). For `k ≥ 1` and a set
`P` of cells of an `r × c` grid (points may share rows and columns): if the rank permutation
`σ_P` contains the board pattern `ρ_k`, then the indicator matrix of `P` has a `k`-grid minor;
consequently, if `P` is `k`-grid-free, `σ_P` avoids `ρ_k`. -/
theorem lemma_6_1 (k : ℕ) (hk : 1 ≤ k) {r c : ℕ} (P : Finset (Fin r × Fin c)) :
    (Contains (rho k) (rankPerm P) → HasGridMinor (indicator P) k) ∧
    (¬ HasGridMinor (indicator P) k → Avoids (rho k) (rankPerm P)) := by sorry

end PatternRangeCounting1593.RangeCounting.Supplement
