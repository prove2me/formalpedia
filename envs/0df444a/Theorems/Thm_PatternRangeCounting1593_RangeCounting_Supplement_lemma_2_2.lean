-- Prove2me | Theorems.Thm_PatternRangeCounting1593_RangeCounting_Supplement_lemma_2_2
-- name    : PatternRangeCounting1593.RangeCounting.Supplement.lemma_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T12:05:29.208682+00:00
-- url     : https://prove2.me/theorems/df922789-7001-4df1-a8c6-85deab7e5601
-- title:
--   Lemma 2.2 — grid-free XOR-difference support
-- statement:
--   Let $t\ge1$. If a binary $r\times c$ matrix $M$ is $t$-mixed-free, then its XOR difference array $D$ is $2t$-grid-free: no division of the rows and of the columns of $D$ into $2t$ consecutive nonempty blocks each puts a one in every one of the $(2t)^2$ zones. Consequently there is a constant $C_t$, depending only on $t$, such that every $t$-mixed-free $r\times c$ binary matrix satisfies
--   $$|\operatorname{supp}(D)|\le C_t\,(r+c).$$
--
--   A zone is mixed if it contains a nonconstant row and a nonconstant column, and $M$ is $t$-mixed-free if no division into $t\times t$ consecutive nonempty blocks makes every zone mixed. The lemma converts this structural restriction on $M$, which may have $\Theta(rc)$ ones, into a linear bound on the support of $D$.
--
--   **Formalization Note** Mixed-freeness and grid minors are the published `TwinWidthI.GridThm.MixedFree` and `TwinWidthI.GridThm.HasGridMinor` (divisions by strictly increasing cut points). The constant $C_t$ is a natural number quantified before $r$, $c$ and $M$.
--
--   Differences from the source:
--   - reading: t-mixed-free for a fixed t (t ≥ 1 implicit) → hypothesis 1 ≤ t; reason: no (0,0)-division of a nonempty matrix exists, so every nonempty matrix is vacuously 0-mixed-free and both conclusions would fail at t = 0; the paper's space-optimality paragraph writes 'every fixed t ≥ 1'
--   - encoding: |supp(D)| = O_t(r + c) → ∃ C : ℕ (depending only on t), ∀ r c M, t-mixed-free → |supp D| ≤ C (r + c); reason: §1.1 subscript convention; the constant is quantified before the instance
--   - encoding: divisions, mixed zones and k-grid minors of Definition 3.1 → the published TwinWidthI.GridThm.MixedFree and HasGridMinor on Matrix (Fin r) (Fin c) Bool; reason: checked equal to Definition 3.1 (IsMixed = neither every column nor every row constant in the zone)
-- source:
--   Sankardeep Chakraborty, STOC 2027 submission #1593 (October 2026), Lemma 2.2, printed p. 9 (PDF p. 10); Definition 3.1, printed p. 10 (PDF p. 11)

import Mathlib
import Definitions.Def_PatternRangeCounting1593_RangeCounting_Perm
import Definitions.Def_PatternRangeCounting1593_RangeCounting_Machine
import Definitions.Def_TwinWidthI_GridThm_Setting
import Definitions.Def_PatternRangeCounting1593_RangeCounting_Supplement_MatrixAccess
set_option autoImplicit false
open PatternRangeCounting1593.RangeCounting TwinWidthI.GridThm

namespace PatternRangeCounting1593.RangeCounting.Supplement

/-- Lemma 2.2 (Grid-free XOR-difference support), printed p. 9 (PDF p. 10). If a binary matrix
`M` is `t`-mixed-free (`t ≥ 1`), its XOR difference array `D` is `2t`-grid-free; and there is a
constant `C` depending only on `t` with `|supp(D)| ≤ C (r + c)` for every `t`-mixed-free
`r × c` matrix. -/
theorem lemma_2_2 :
    (∀ t : ℕ, 1 ≤ t → ∀ (r c : ℕ) (M : Matrix (Fin r) (Fin c) Bool),
      MixedFree M t → ¬ HasGridMinor (xorDiff M) (2 * t)) ∧
    (∀ t : ℕ, 1 ≤ t → ∃ C : ℕ, ∀ (r c : ℕ) (M : Matrix (Fin r) (Fin c) Bool),
      MixedFree M t → (supp (xorDiff M)).card ≤ C * (r + c)) := by sorry

end PatternRangeCounting1593.RangeCounting.Supplement
