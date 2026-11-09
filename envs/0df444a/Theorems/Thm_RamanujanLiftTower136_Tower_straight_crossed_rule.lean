-- Prove2me | Theorems.Thm_RamanujanLiftTower136_Tower_straight_crossed_rule
-- name    : RamanujanLiftTower136.Tower.straight_crossed_rule
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:39:54.255477+00:00
-- url     : https://prove2.me/theorems/e1ae6482-c1d4-4992-8c39-d768bf04bb49
-- title:
--   Proposition 6.2 — straight/crossed rule and signed decomposition
-- statement:
--   For an admissible prime $p$ and a level $n\ge1$, let $y=f_j(t)\bmod2^n$. With the sheet labeling $t+b2^n\leftrightarrow(t,b)$,
--   $$\operatorname{Rot}_{n+1,p}((t,b),j)=((y,b\oplus\beta_n(t,j)),j^*).$$
--   Moreover $\beta_n(t,j)=\beta_n(y,j^*)$. For the signed adjacency $B_{n,p}$ with signs $(-1)^{\beta_n(t,j)}$,
--   $$A_{n+1,p}\simeq A_{n,p}\oplus B_{n,p},\qquad\|B_{n,p}\|\le2\sqrt p.$$
--   The equivalence is orthogonal for the counting inner product. The explicit normalized even/odd map is bijective, preserves squared norm, and intertwines the two operators. All clauses, including the signed norm bound, belong to this one item.
--
--   Differences from the source:
--   - encoding: the fixed arithmetic objects and labeled graphs → the shared concrete definitions over the quadratic algebra, ZMod residues, and zero-based Fin label indices; reason: the representations preserve the field, orders, incidences, and all source instances
--   - encoding: orthogonal equivalence and operator norm → the normalized fiber-even/odd transform, preservation of sum of squares, intertwining, and the equivalent squared-norm inequality for every real function; reason: this gives the claimed orthogonal equivalence and exact counting-operator norm bound without a default supremum
-- source:
--   Olga Kharlampovich, Igor Pak, Alina Vdovina, STOC 2027 submission #136 (October 2026), source.pdf SHA-256 27d691a82d8af863e511e7e6b00cee95779d914645846d2974f876836db8f83b, p.20 (PDF p.21), Proposition 6.2. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/136.pdf

import Definitions.Def_RamanujanLiftTower136_Tower_Graphs

namespace RamanujanLiftTower136.Tower

theorem straight_crossed_rule (p n : ℕ) (hp : admissible p) (hn : 1 ≤ n) :
  liftRule p n ∧ reverseBitRule p n ∧ signedDecomposition p n := by sorry

end RamanujanLiftTower136.Tower
