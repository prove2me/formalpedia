-- Prove2me | Theorems.Thm_UniformSubpower_Supplied_theorem_4_1
-- name    : UniformSubpower.Supplied.theorem_4_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T05:20:40.618731+00:00
-- url     : https://prove2.me/theorems/1fc2e200-d52c-4a96-9f30-b99a5b3f2390
-- title:
--   Theorem 4.1 — all proper meet-irreducibles of a finite modular lattice from its d join-irreducibles with O(d⁵) lattice and order operations
-- statement:
--   Let $L$ be a finite modular lattice whose lattice and order operations are available, and suppose the complete list $J = J(L)$ of its nonzero join-irreducibles is given, with $d = |J|$. Then all proper meet-irreducibles $M(L)$ can be enumerated using $O(d^5)$ lattice and order operations, without enumerating $L$. Precisely: there are a universal constant $C$ and, for every $d$, a program over lattice and order operations such that for every finite modular lattice $L$ and every duplicate-free list $J$ of exactly the nonzero join-irreducibles of $L$, the program for $d = |J|$, started on the store $\bot, \top, J$, returns a duplicate-free list whose elements are exactly $M(L)$ and performs
--   $$\#\{\text{joins, meets, comparisons}\} \le C\,(d+1)^5 .$$
--
--   In the paper this is the step that enumerates the meet-irreducible congruences of each coordinate projection, whose congruence lattice is modular because of the Mal'tsev operation, in time polynomial in the full tables although the congruence lattice may be exponentially large.
--
--   **Formalization Note.** The program is a `LatProg`: it sees lattice elements only through handles, and `LatProg.run` counts every join, meet and comparison. $C$ is quantified before the lattice, so it is universal.
--
--   Differences from the source:
--   - reading: "using O(d⁵) lattice and order operations, without enumerating L" for a lattice whose elements have polynomial-size encodings → a program over a handle store that interacts with L only through join, meet and ≤, one program per d, whose number of such operations is counted; reason: the claim is an operation count (bookkeeping is not charged in the source either), and a count independent of |L| excludes enumerating L.
--   - reading: the given list J → the initial store ⊥, ⊤, J; reason: the source's algorithm uses the constants 0 and 1 (the tests (3) include 0, and ⋀∅ = 1).
--   - encoding: O(d⁵) → at most C·(d+1)⁵ with a universal constant C; reason: equal to C·d⁵ up to the factor 32 for d ≥ 1, and allows a constant cost for the singleton lattice (d = 0), which the source handles directly.
-- source:
--   Gkantzounis, Uniform Subpower Membership for Finite Mal'tsev Algebras, STOC 2027 submission (manuscript sha256 149e66b1…), p. 13, Theorem 4.1

import Mathlib
import Definitions.Def_UniformSubpower_Supplied_LatticeOracle

universe u

namespace UniformSubpower.Supplied

/-- Theorem 4.1 (Gkantzounis, p. 13): modular meet-irreducible enumeration. There is a universal
constant `C` and, for every `d`, one program over the lattice and order operations such that for
every finite modular lattice `L` and every duplicate-free list `J` of exactly its nonzero
join-irreducibles with `d = |J|`, the program started on the store `[⊥, ⊤] ++ J` returns handles
of a duplicate-free list of exactly the proper meet-irreducibles of `L`, using at most
`C · (d + 1)⁵` lattice and order operations. -/
theorem theorem_4_1 :
    ∃ C : ℕ, ∃ alg : ℕ → LatProg (List ℕ),
      ∀ (L : Type u) [Lattice L] [BoundedOrder L] [Fintype L] [IsModularLattice L]
        (J : List L), J.Nodup → (∀ x : L, x ∈ J ↔ SupIrred x) →
        ((readHandles ((alg J.length).run ([⊥, ⊤] ++ J)).2.1
            ((alg J.length).run ([⊥, ⊤] ++ J)).1).Nodup ∧
          (∀ x : L, x ∈ readHandles ((alg J.length).run ([⊥, ⊤] ++ J)).2.1
            ((alg J.length).run ([⊥, ⊤] ++ J)).1 ↔ InfIrred x) ∧
          ((alg J.length).run ([⊥, ⊤] ++ J)).2.2 ≤ C * (J.length + 1) ^ 5) := by sorry

end UniformSubpower.Supplied
