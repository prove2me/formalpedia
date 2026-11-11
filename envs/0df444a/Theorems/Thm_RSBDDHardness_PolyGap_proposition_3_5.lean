-- Prove2me | Theorems.Thm_RSBDDHardness_PolyGap_proposition_3_5
-- name    : RSBDDHardness.PolyGap.proposition_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:26:57.403985+00:00
-- url     : https://prove2.me/theorems/d9f669f9-9013-46fe-9b48-3b9a20f82469
-- title:
--   Proposition 3.5 — Exact 1-in-3-SAT as vector subset sum
-- statement:
--   Let $\varphi$ be a monotone Exact 1-in-3 formula with variables $z_1,\dots,z_m$ and clauses $C_1,\dots,C_c$ in which every clause contains three distinct variables. Let $q\ge3$ be prime and let $v_{i,b}\in\mathbb F_q^{m+c}$ and $T=(1^m;1^c)$ be the vectors of (11). For every set $I\subseteq[m]\times\{0,1\}$,
--   $$\sum_{(i,b)\in I}v_{i,b}=T\iff I=\{(i,b_i):i\in[m]\}\text{ for an Exact 1-in-3 satisfying assignment }(b_1,\dots,b_m).$$
--   In particular every solution has $|I|=m$.
--
--   This is the Boolean interface of the reduction: the first moment of an MSS solution, after the quotient map, is exactly such a vector sum.
--
--   Differences from the source:
--   - generalization: nonempty cubic planar monotone formulas with m variables and m clauses; vectors in F_q^{2m} → any monotone formula with c clauses of three distinct variables, including the empty formula; vectors in F_q^{m+c}; reason: the proof uses only distinctness within each clause; it needs neither cubic occurrences nor planarity nor nonemptiness, and every source formula is included
--   - encoding: I contains exactly one pair (i, b_i) for every variable i → I is the image of i ↦ (i, b i) for an assignment b; reason: same sets
--   - encoding: variables z_1..z_m, clauses C_1..C_m → indices in Fin m and positions in the clause list (0-based); reason: renaming only
-- source:
--   Daqing Wan, Jun Zhang, NP-Hardness of Bounded Distance Decoding for Reed–Solomon Codes, STOC 2027 submission #449 (October 2026), Proposition 3.5, eqs. (11)–(12), PDF p. 13 (printed p. 12); PDF SHA-256 d60d9a54b73aa972494f130439dc6e07f8c7b33556741f8324d22cf45218e22b

import Mathlib
import Definitions.Def_RSBDDHardness_PolyGap_Algebra
set_option autoImplicit false
open scoped BigOperators
open Classical

namespace RSBDDHardness.PolyGap

/-- Proposition 3.5 (Exact 1-in-3-SAT as vector subset sum), PDF 13. For a monotone formula
whose clauses each contain three distinct variables and a prime `q ≥ 3`, a set
`I ⊆ [m] × {0,1}` satisfies `∑_{(i,b) ∈ I} v_{i,b} = T` iff `I` selects exactly one pair
`(i, b_i)` per variable and `(b_i)` is an Exact 1-in-3 satisfying assignment; every solution
has cardinality `m`. -/
theorem proposition_3_5 (φ : OneInThree) (q : ℕ) (hq : q.Prime) (hq3 : 3 ≤ q)
    (hφ : φ.DistinctClauses) (I : Finset (Fin φ.m × Bool)) :
    ((∑ p ∈ I, φ.vec q p.1 p.2) = φ.target q ↔
        ∃ b : Fin φ.m → Bool, I = Finset.univ.image (fun i => (i, b i)) ∧ φ.ExactSat b) ∧
      ((∑ p ∈ I, φ.vec q p.1 p.2) = φ.target q → I.card = φ.m) := by sorry

end RSBDDHardness.PolyGap
