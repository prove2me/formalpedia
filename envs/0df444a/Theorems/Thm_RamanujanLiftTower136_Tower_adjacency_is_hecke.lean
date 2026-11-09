-- Prove2me | Theorems.Thm_RamanujanLiftTower136_Tower_adjacency_is_hecke
-- name    : RamanujanLiftTower136.Tower.adjacency_is_hecke
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:39:37.133859+00:00
-- url     : https://prove2.me/theorems/bf5897fd-a755-4db9-8652-6678814f01fd
-- title:
--   Proposition 4.2 — adjacency is the unnormalized Hecke operator
-- statement:
--   Let $p\equiv1\pmod{17}$ be prime and $n\ge1$. Under the named bijection $t\mapsto[I_t]$ from (3.13), adjacency is the Hecke operator on the entire ideal-class set:
--   $$A_{n,p}(h\circ[I_\cdot])(t)=(T_Ph)([I_t]).$$
--   Here $T_P$ sums over actual locally principal ideals $J\subset I$ unchanged away from $P$ and satisfying $\operatorname{nrd}(J)=P\operatorname{nrd}(I)$. Each such ideal contributes once, even when its class coincides with another neighbor class. The statement also records that there are exactly $p+1$ such ideals for every representative $I$. This is the link between the constructed graph and the independent arithmetic operator.
--
--   Differences from the source:
--   - encoding: the fixed arithmetic objects and labeled graphs → the shared concrete definitions over the quadratic algebra, ZMod residues, and zero-based Fin label indices; reason: the representations preserve the field, orders, incidences, and all source instances
--   - encoding: functions on the ideal-class set and a finite neighbor sum → functions on the ambient orbit quotient restricted to the actual class set, with finite neighbor sets of cardinality p+1 asserted; reason: every function on the class set extends to this ambient set; explicit finiteness guards the finite-support sum
-- source:
--   Olga Kharlampovich, Igor Pak, Alina Vdovina, STOC 2027 submission #136 (October 2026), source.pdf SHA-256 27d691a82d8af863e511e7e6b00cee95779d914645846d2974f876836db8f83b, p.17 (PDF p.18), Proposition 4.2. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/136.pdf

import Definitions.Def_RamanujanLiftTower136_Tower_Ideals
import Definitions.Def_RamanujanLiftTower136_Tower_Graphs

namespace RamanujanLiftTower136.Tower

theorem adjacency_is_hecke (p n : ℕ) (hp : admissible p) (hn : 1 ≤ n) :
  Set.BijOn (vertexClass n) Set.univ (classSet (levelOrder n)) ∧
  (∀ I : Set D, locallyPrincipal (levelOrder n) I →
    {J : Set D | primeNeighbor p (levelOrder n) I J}.Finite ∧
    Nat.card {J : Set D // primeNeighbor p (levelOrder n) I J} = p+1) ∧
  ∀ (h : IdealClass → ℂ) (t : Vertex n),
    adjacency p n (fun s => h (vertexClass n s)) t =
      hecke p (levelOrder n) h (vertexClass n t) := by sorry

end RamanujanLiftTower136.Tower
