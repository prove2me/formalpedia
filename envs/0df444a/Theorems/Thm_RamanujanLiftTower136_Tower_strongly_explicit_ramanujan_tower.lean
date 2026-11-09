-- Prove2me | Theorems.Thm_RamanujanLiftTower136_Tower_strongly_explicit_ramanujan_tower
-- name    : RamanujanLiftTower136.Tower.strongly_explicit_ramanujan_tower
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:46:10.109164+00:00
-- url     : https://prove2.me/theorems/3d5e84d3-d94c-4f56-be1c-aa18bc428be0
-- title:
--   Theorem 1.1 — strongly explicit Ramanujan towers, all clauses
-- statement:
--   For every prime $p\equiv1\pmod{17}$, take the concrete generator list and dyadic neighbor maps defined in §§3–4 and §7. They have exactly $d=p+1$ labels with an involutive reverse-edge pairing. For every $n\ge1$, these maps define a connected labeled multigraph $\Gamma_{n,p}$ on exactly $\mathbb Z/2^n\mathbb Z$, with $2^n$ vertices and degree $d$, preserving all parallel edges, loops, and half-loops.
--
--   The adjacency matrix is symmetric and every eigenvalue $\lambda<d$ satisfies
--   $$|\lambda|\le2\sqrt p.$$
--   The graph is non-bipartite and hence Ramanujan with the exact threshold $2\sqrt{d-1}$. Reduction modulo $2^n$ is a label-preserving two-sheeted cover from level $n+1$. The specified lift bit gives the straight/crossed rule and agrees on reversed orientations.
--
--   For each fixed $p$ there are a finite-alphabet multi-stack machine and $C_p>0$, independent of $n,t,j$, computing either the $n$-bit neighbor or the one-bit lift answer in at most $C_pn^3$ steps. The machine receives the level through its input length, the vertex bits, a fixed-width label, and a mode bit; there is no level-dependent advice. This one item states all four parts of Theorem 1.1 and the structural conclusions that make its total definitions valid.
--
--   Differences from the source:
--   - encoding: the fixed arithmetic objects and labeled graphs → the shared concrete definitions over the quadratic algebra, ZMod residues, and zero-based Fin label indices; reason: the representations preserve the field, orders, incidences, and all source instances
--   - reading: lexicographically first and lexicographically sorted integer coordinates → the usual signed-integer lexicographic order on pairs and eight-tuples; reason: the paper does not specify the order on signed coordinate vectors more explicitly
--   - reading: bit operations → steps of a finite-alphabet finite-control multi-stack machine with the stated binary encodings; reason: schoolbook arithmetic and bitwise Hensel lifting retain the cubic bound; fixed-prime lookup is absorbed only in its permitted constant
--   - encoding: degree, undirectedness, and the two-sheeted signed cover → explicit label count, neighbor bijectivity, inverse labels, row sums, symmetric adjacency, fiber cardinalities, and both bit identities; reason: these are conclusions documenting the source graph conventions and prevent total-function defaults from trivializing the target
--   - encoding: O_p(n³) → for each admissible p a machine and positive C_p bounding every valid query by C_p n³; reason: the quantifier order allows dependence on p only
--   - encoding: every adjacency eigenvalue λ < d (complex eigenvalues and eigenvectors) → real λ with a nonzero real eigenfunction, together with symmetry of the adjacency matrix as a conclusion; reason: a real symmetric matrix has only real eigenvalues with real eigenvectors, so the two formulations agree on every instance
-- source:
--   Olga Kharlampovich, Igor Pak, Alina Vdovina, STOC 2027 submission #136 (October 2026), source.pdf SHA-256 27d691a82d8af863e511e7e6b00cee95779d914645846d2974f876836db8f83b, p.1 (PDF p.2), Theorem 1.1. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/136.pdf

import Definitions.Def_RamanujanLiftTower136_Tower_Graphs
import Definitions.Def_RamanujanLiftTower136_Tower_Computation

namespace RamanujanLiftTower136.Tower

theorem strongly_explicit_ramanujan_tower (p : ℕ) (hp : admissible p) :
  (labels p).length = p+1 ∧ Function.Involutive (reverse p) ∧
  stronglyExplicit p ∧ ∀ n : ℕ, 1 ≤ n →
    (graph p n).Valid ∧ Nat.card (Vertex n) = 2^n ∧
    (∀ t : Vertex n, ∑ s : Vertex n, (graph p n).matrix t s = (p+1 : ℝ)) ∧
    (graph p n).Connected ∧ spectralConclusion p n ∧
    (graph p n).TwoCover (graph p (n+1)) (reduction n) ∧
    liftRule p n ∧ reverseBitRule p n := by sorry

end RamanujanLiftTower136.Tower
