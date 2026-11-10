-- Prove2me | Theorems.Thm_UniformSubpower_Supplied_theorem_1_1
-- name    : UniformSubpower.Supplied.theorem_1_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T05:21:23.109993+00:00
-- url     : https://prove2.me/theorems/71bb43b2-e997-4ec2-a9b2-5938f68a4e32
-- title:
--   Theorem 1.1 — uniform subpower membership with a supplied common Mal'tsev operation in deterministic polynomial time
-- statement:
--   Let $A_0, \dots, A_{n-1}$ be finite nonempty algebras in one indexed signature, supplied by full tables, with a designated basic ternary operation $m$ satisfying $m(x, y, y) = x$ and $m(x, x, y) = y$ in every coordinate, and let $G \subseteq \prod_i A_i$ be a finite list of generators. From the instance one can prepare, in deterministic time polynomial in its encoding length $N$, a predicate deciding membership in every selected-coordinate projection of $\mathrm{Sg}(G)$, and each subsequent query is answered in deterministic time polynomial in $N + R$, $R$ the query length. Precisely: there are functions $\mathsf{prepare}$ on bitstrings and $\mathsf{answer}$ on pairs of bitstrings, both computable in polynomial time by deterministic Turing machines with one fixed polynomial each, such that for every valid instance $I$ and every query $Q$ (a list of prescriptions $(i, a)$),
--   $$\mathsf{answer}\big(\mathsf{prepare}(\langle I \rangle), \langle Q \rangle\big) = \mathsf{true} \iff \exists\, b \in \mathrm{Sg}(G)\ \ \forall (i, a) \in Q:\ i < n \text{ and } b_i = a .$$
--   The polynomials do not depend on the algebras, the signature, the arities, the carrier sizes or $n$.
--
--   This is the paper's main theorem. It decides the subpower membership problem for Mal'tsev algebras uniformly in the input tables, and it implies that subpower membership is in P for every fixed finite Mal'tsev algebra (Willard's question) and that minority-term detection for finite idempotent algebras is in P.
--
--   **Formalization Note.** $\langle I \rangle$ = `encodeInstance I` and $\langle Q \rangle$ = `encodeQuery Q`; polynomial time is `PvsNP.IsPolyTime` (Mathlib's `TM2ComputableInPolyTime` on canonical bitstring encodings). Since $\mathsf{prepare}$ runs in polynomial time its output has length polynomial in $N$, so the time of $\mathsf{answer}$, polynomial in its input length, is polynomial in $N + R$. Correctness is required on encodings of valid instances; outputs on other bitstrings are unconstrained.
--
--   Differences from the source:
--   - encoding: deterministic time on a word RAM with O(log N)-bit words (§14) → deterministic multi-stack Turing machines (`PvsNP.IsPolyTime`); reason: both define the same polynomial-time functions.
--   - encoding: input of explicit encoding length N, query of length R → `encodeInstance` (binary numbers in self-delimiting blocks, every table in full in lexicographic order, generators entry by entry) and `encodeQuery`; reason: length-faithful, so the lengths are within constant factors of N and R.
--   - encoding: a prepared predicate, then queries in time poly(N + R) → `prepare` and `answer` on (prepare(⟨I⟩), ⟨Q⟩), both polynomial-time; reason: answer's input has length polynomial in N plus O(R).
--   - encoding: queries prescribing values on selected coordinates, malformed or conflicting prescriptions rejected → lists of pairs (i, a), positive iff one tuple of Sg(G) satisfies all; reason: covers every selected-coordinate projection and full targets; malformed and conflicting queries are exactly the negative ones the source rejects.
--   - encoding: algebras A₁, …, A_n with carriers, symbols and the designated operation → coordinates 0..n−1 with carriers Fin sᵢ, symbols by index, the designated symbol by its index; correctness on valid encodings only; reason: relabelling; the source validates the tables (§12) and claims nothing about invalid inputs.
-- source:
--   Gkantzounis, Uniform Subpower Membership for Finite Mal'tsev Algebras, STOC 2027 submission (manuscript sha256 149e66b1…), p. 4, Theorem 1.1

import Mathlib
import Definitions.Def_PvsNP_bitstring_encoding
import Definitions.Def_PvsNP_complexity_classes
import Definitions.Def_UniformSubpower_Supplied_Algebra
import Definitions.Def_UniformSubpower_Supplied_Encoding

namespace UniformSubpower.Supplied

/-- Theorem 1.1 (Gkantzounis, p. 4): uniform subpower membership with a supplied common
Mal'tsev operation, with a polynomial-time preparation and polynomial-time queries. One pair of
deterministic polynomial-time machines (one polynomial each) serves every valid instance and every
query. -/
theorem theorem_1_1 :
    ∃ (prepare : List Bool → List Bool) (answer : List Bool × List Bool → Bool),
      PvsNP.IsPolyTime prepare ∧ PvsNP.IsPolyTime answer ∧
      ∀ I : Instance, I.Valid → ∀ Q : Query,
        (answer (prepare (encodeInstance I), encodeQuery Q) = true ↔ I.Positive Q) := by sorry

end UniformSubpower.Supplied
