-- Prove2me | Theorems.Thm_SubcubicBA_PlainPKI_theorem_11
-- name    : SubcubicBA.PlainPKI.theorem_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T15:43:06.863409+00:00
-- url     : https://prove2.me/theorems/e25e1a85-c0cd-48bd-af47-12d6cce5dcdb
-- title:
--   Theorem 11 — explicit dispersers of out-degree m
-- statement:
--   Fix a constant $0<\alpha<1$. There is an explicit family of directed graphs $G_{n,m}$, for $1\le m\le n$, on $n$ vertices such that every vertex has exactly $m$ distinct out-neighbours (self-loops allowed) and $G_{n,m}$ is an $(\alpha n,\; n-4\alpha^{-1}n/m)$-disperser: every set $S$ of at least $\alpha n$ vertices satisfies
--   $$|N(S)|\ge n-\frac{4n}{\alpha m}.$$
--   Explicit means that the map $(n,m)\mapsto G_{n,m}$, with parameters in unary and output the adjacency bit matrix, is computed by a Turing machine in polynomial time.
--
--   Such dispersers spread votes and proofs in SpreadVotes and ValidatedDispersion so that every large set of parties jointly receives almost everything.
--
--   Differences from the source:
--   - encoding: explicit: constructed deterministically in polynomial time (p. 37) → one function from the parameters in unary to the adjacency bit matrix, computed by a Turing machine in polynomial time (TM2ComputableInPolyTime); reason: the paper's definition of explicit; unary parameters make the time polynomial in n
--   - reading: each vertex has out-degree m → exactly m distinct out-neighbours, self-loops allowed; reason: the strongest reading; the proof's multigraph construction can be padded since m ≤ n
--   - encoding: (αn, n − 4α⁻¹n/m) → real-valued thresholds; reason: same instances
-- source:
--   Marc Dufay, Roger Wattenhofer, Optimal Subcubic Byzantine Agreement with Plain PKI, STOC 2027 submission #101 (October 2026), Theorem 11, p. 37

import Mathlib
import Definitions.Def_SubcubicBA_PlainPKI_Graphs

namespace SubcubicBA.PlainPKI

/-- Theorem 11 (p. 37). -/
theorem theorem_11 (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ f : ℕ × ℕ → List Bool, PolyTimeFamily unary2 f ∧
      ∀ n m : ℕ, 1 ≤ m → m ≤ n →
        (f (n, m)).length = n * n ∧
        (∀ u : Fin n, (nbhdOfBits (f (n, m)) n n u).card = m) ∧
        IsDisperser (nbhdOfBits (f (n, m)) n n) (α * n) ((n : ℝ) - 4 * α⁻¹ * n / m) := by sorry

end SubcubicBA.PlainPKI
