-- Prove2me | Theorems.Thm_RelQueryPTime_cell_tableau
-- name    : RelQueryPTime.cell_tableau
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:40:41.361207+00:00
-- url     : https://prove2.me/theorems/315b1d40-d8e3-4f50-b890-9e29b8765ab7
-- title:
--   Proof of Theorem 1 — the tableau rule $\langle a_{-1}a_0a_1\rangle \to a$
-- statement:
--   Let $M$ be a one-tape Turing machine (Cook's model) and $w$ an input. Number the tape cells by $\mathbb Z$, the input starting at cell $0$. In the run of $M$ on $w$:
--
--   1. at time $0$, cell $0$ carries the initial state $q_0$, cell $j \ge 0$ carries the input symbol $w_j$ (blank beyond the input), and every cell $j < 0$ is blank;
--   2. for every time $t$ and cell $j$,
--   $$
--   \mathrm{Cell}(t+1, j) = \big\langle \mathrm{Cell}(t, j-1)\ \mathrm{Cell}(t, j)\ \mathrm{Cell}(t, j+1)\big\rangle \to \cdot,
--   $$
--   i.e. the content of cell $j$ after one move is determined by the contents of cells $j-1$, $j$, $j+1$ before it, through the one-move rule of $M$.
--
--   This locality is what lets a first-order formula build the computation of $M$ row by row. The statement also ties the tableau to Cook's step function.
--
--   Differences from the source:
--   - reading: the triple <a−1a0a1> leads to the symbol a in one move of M → an explicit one-move function on cell contents (state or no head, symbol) of Cook's one-tape machine, cells numbered by ℤ, with the initial row stated as well; reason: the page fixes no machine model; Cook's tape is two-way infinite (blanks are added at the left end), so cells are numbered by ℤ
-- source:
--   N. Immerman, Relational Queries Computable in Polynomial Time (Extended Abstract), Proc. 14th ACM STOC, 1982, pp.147–152, doi:10.1145/800070.802187, proof of Theorem 1, p.149 ("Here '<a-1a0a1>→a' means that the triple <a-1a0a1> leads to the symbol a in one move of M.") (PDF p.3)

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_RelQueryPTime_Machine

namespace RelQueryPTime

/-- The tableau of a run (Immerman, *Relational Queries Computable in Polynomial Time*, STOC 1982, proof of Theorem 1, p.149: "Here `<a-1a0a1>→a` means that the triple
`<a-1a0a1>` leads to the symbol `a` in one move of M"). For Cook's one-tape machine `M` and input
`w`, the cell contents of the run `TM.run`
1. at time `0` are: the state `q₀` on cell `0`, and the input symbol `w_j` on cell `j ≥ 0`
   (blank elsewhere);
2. at time `t + 1` on cell `j` are obtained from the contents of cells `j-1, j, j+1` at time `t` by
   one move of `M` (`leads`).

**Formalization Note** Cells are numbered by their absolute position in `ℤ`, the input starting at
`0`; the machine's tape is two-way infinite. -/
theorem cell_tableau {Γ : Type} (M : CookPvsNP.TM Γ) (w : List Γ) :
    (∀ j : ℤ, cell M w 0 j = (if j = 0 then some M.q₀ else none,
      if 0 ≤ j then w[j.toNat]? else none)) ∧
    ∀ (t : ℕ) (j : ℤ), cell M w (t + 1) j =
      leads M (cell M w t (j - 1)) (cell M w t j) (cell M w t (j + 1)) := by sorry

end RelQueryPTime
