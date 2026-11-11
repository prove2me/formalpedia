-- Prove2me | Theorems.Thm_PatternRangeCounting1593_RangeCounting_lemma_4_1
-- name    : PatternRangeCounting1593.RangeCounting.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:11:59.060117+00:00
-- url     : https://prove2.me/theorems/84c24b45-bbe9-438c-b7b1-3ccf11e21deb
-- title:
--   Lemma 4.1 — four-region identity
-- statement:
--   Let $\tau$ be a permutation of length $m$ with nested row and column divisions, and let $E=C\times R$ be a cell at some level $i$ (occupied or not). Let $\kappa_E(x,y)=|P_\tau\cap([\min C,x]\times[\min R,y])|$. For $\min C-1\le x\le\max C$ and $\min R-1\le y\le\max R$,
--   $$\mathrm{Count}_\tau(x,y)=p(E)+G_C\bigl(x,c(E)\bigr)+G_R\bigl(y,d(E)\bigr)+\kappa_E(x,y).\tag{5}$$
--   In particular, $\kappa_E(x,y)=0$ when $E$ is empty.
--
--   The identity reduces a dominance query to the state of any containing cell plus two boundary prefixes and the part inside the cell.
--
--   Differences from the source:
--   - encoding: a cell E = C × R → level i ≤ ℓ, column block b and row block b′ of a valid pair of nested division chains; G_R is G of the transposed view; reason: explicit indexing of cells
--   - generalization: the pattern-avoiding permutation and retained hierarchy fixed at the start of Section 4 → any permutation and any valid nested row and column divisions; reason: the four disjoint regions use only the interval partitions; the source hierarchy is one such pair of divisions
-- source:
--   Sankardeep Chakraborty, STOC 2027 submission #1593 (October 2026), Lemma 4.1 and Equation (5), printed p. 14 (PDF p. 15)

import Mathlib
import Definitions.Def_PatternRangeCounting1593_RangeCounting_Perm
import Definitions.Def_PatternRangeCounting1593_RangeCounting_Machine
import Definitions.Def_PatternRangeCounting1593_RangeCounting_Hierarchy
import Definitions.Def_PatternRangeCounting1593_RangeCounting_KOInterface
import Definitions.Def_PatternRangeCounting1593_RangeCounting_IndexSpecs
set_option autoImplicit false
open Filter Topology
open Classical

namespace PatternRangeCounting1593.RangeCounting

/-- Lemma 4.1 (Four-region identity). -/
theorem lemma_4_1 {m : ℕ} (τ : Equiv.Perm (Fin m)) (Hd : Hierarchy) (hHd : Hd.Valid m)
    (i : ℕ) (hi : i ≤ Hd.ell) (b b' : ℕ) (hb : b < numBlocks Hd.cb m i)
    (hb' : b' < numBlocks Hd.rb m i) (x y : ℕ)
    (hx₁ : bmin Hd.cb m i b ≤ x + 1) (hx₂ : x ≤ bmax Hd.cb m i b)
    (hy₁ : bmin Hd.rb m i b' ≤ y + 1) (hy₂ : y ≤ bmax Hd.rb m i b') :
    Count τ x y = nwCount (colView τ Hd) i b b'
        + Gpref (colView τ Hd) i b x (cutAbove (colView τ Hd) i b b')
        + Gpref (rowView τ Hd) i b' y (cutAbove (rowView τ Hd) i b' b)
        + kappa (colView τ Hd) i b b' x y ∧
      (¬ occ (colView τ Hd) i b b' → kappa (colView τ Hd) i b b' x y = 0) := by sorry

end PatternRangeCounting1593.RangeCounting
