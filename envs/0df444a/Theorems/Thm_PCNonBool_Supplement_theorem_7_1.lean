-- Prove2me | Theorems.Thm_PCNonBool_Supplement_theorem_7_1
-- name    : PCNonBool.Supplement.theorem_7_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:30:09.80809+00:00
-- url     : https://prove2.me/theorems/fa47d796-7bc7-4f72-b8bc-9f0d342da70a
-- title:
--   Theorem 7.1 — automating PCR with $\{\pm1\}$-variables is NP-hard
-- statement:
--   **Theorem 7.1.** Let $\mathcal P$ denote polynomial calculus resolution supplied with $\{\pm1\}$-valued variables. There are a polynomial-time algorithm $A$ mapping CNF formulas to CNF formulas and constants $C,d\in\mathbb N$, $\varepsilon>0$ such that for every field $\mathbb F$ with $\operatorname{char}\mathbb F\ne2$ and every $n$-variable CNF formula $F$ with $|F|$ clauses:
--
--   1. if $F$ is satisfiable, then $A(F)$ is unsatisfiable and has a polynomial calculus refutation over $\mathbb F$ (over $\{0,1\}$-valued variables) of size at most $C(|F|+1)^d$;
--   2. if $F$ is unsatisfiable, then every $\mathcal P$-refutation $\pi$ of $A(F)$ over $\mathbb F$ has size
--   $$|\pi|\ \ge\ \exp(\varepsilon n^2).$$
--
--   In particular, if $\mathcal P$ over $\mathbb F$ is automatable in polynomial time, then CNF satisfiability is decidable in polynomial time, i.e. $\mathrm P=\mathrm{NP}$.
--
--   The reduction separates satisfiable from unsatisfiable formulas by a polynomial-versus-exponential gap in refutation size, so an automating algorithm run for polynomially many steps decides satisfiability.
--
--   Differences from the source:
--   - reading: a polynomial-time algorithm A mapping CNF formulas to CNF formulas → a function A : CNF → CNF with Nonempty (Turing.TM2ComputableInPolyTime encodeCNF encodeCNF A): a Mathlib two-stack Turing machine computing A in time polynomial in the length of the binary encoding encodeCNF; reason: the paper fixes no machine model; Mathlib's TM2 model with a linear-size injective binary encoding is a standard one
--   - reading: size poly(|F|) and size at least exp(Ω(n²)) → C·(|F| + 1)^d and exp(ε·n²), with C, d ∈ ℕ and ε > 0 chosen after A and before the field and the formula; reason: the constants of the paper's proof do not depend on the field or the formula; |F| + 1 keeps the bound meaningful for the empty formula
--   - encoding: an n-variable CNF formula F with |F| clauses → a list of clauses, each a list of literals (v, sign) over variables v ∈ ℕ; |F| = the length of the list; n = |Vars(F)|, the number of distinct variables occurring; reason: Lean convention; Definition 7.2 indexes the clauses F_1, …, F_m
--   - encoding: part 1: a polynomial calculus refutation of A(F) over {0, 1}-valued variables → PCNonBool.IsRefutation LinearMap.id (pcAxiomsCNF F (A F)): clause C ↦ ∏_{x ∈ C}(1 − x)·∏_{¬x ∈ C} x (1 = true) with the Boolean axioms x² − x for the variables of A(F); axiom lines may be scalar multiples, the refutation contains 1, no reduction; reason: the standard Boolean encoding (p.11); the scaled-axiom and contains-1 conventions change sizes by a factor at most 2, absorbed by C
--   - generalization: polynomial calculus: axiom lines are axioms of the set refuted → the base model PCNonBool.IsDerivation: an axiom line may be any scalar multiple c·red(a) of a reduced axiom a, c = 0 allowed; reason: every standard refutation is one of these, so a lower bound over this larger system implies the paper's
--   - encoding: part 2: P = PCR with {±1}-variables over F, char F ≠ 2; no monomial contains a variable and its dual; lines in the quotient ring → variables (v, 0) = w, (v, 1) = w̄, (v, 2) = w^F; axioms w² − w, w̄² − w̄, w + w̄ − 1, w^F − (1 − 2w), (w^F)² − 1 for v ∈ Vars(A(F)) and the PCR clause monomials ∏_{x ∈ C} x̄·∏_{¬x ∈ C} x; lines reduced by redP (w² = w, w̄² = w̄, (w^F)² = 1, w·w̄ = 0); size counts the monomials of the reduced lines; reason: the paper's definition of P (pp.50, 52–53) and its lower-bound convention (p.11), which only strengthens a size lower bound
--   - generalization: P is automatable: an algorithm outputs a P-refutation of every unsatisfiable F in time polynomial in the smallest P-refutation size plus the size of F → IsAutomatable F: a TM2 machine and a polynomial q such that on every unsatisfiable G it halts within q(S(G) + |enc G|) steps and outputs the monomial structure (lines → monomials → variables) of some P-refutation of G; the coefficients need only exist; reason: elements of an arbitrary field have no finite encoding; outputting only the monomials is a weaker hypothesis (an automating algorithm in any encoding that lists the monomials yields one by deleting the coefficients in linear time), so the implication is at least as strong as the paper's
--   - reading: P = NP → SATinP: CNF satisfiability is decided by a TM2 machine in polynomial time on encodeCNF; reason: Mathlib has no class NP; by the Cook–Levin theorem the two are equivalent, and deciding 3-SAT is the paper's own argument (p.52)
--   - encoding: any field F → F : Type (universe 0); reason: Lean convention; the constant precedes the quantifier over fields, so they range over one universe; a refutation over F uses finitely many scalars, hence is a refutation of the same size over the countable subfield they generate, which is isomorphic to a field in Type
-- source:
--   Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, On the Power of Polynomial Calculus over Non-Boolean Domains, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), Theorem 7.1, p.50 (PDF p.53); proof, p.52 (PDF p.55)

import Mathlib
import Definitions.Def_PCNonBool_IsRefutation
import Definitions.Def_PCNonBool_pcSize
import Definitions.Def_PCNonBool_Supplement_CNF
import Definitions.Def_PCNonBool_Supplement_encodeCNF
import Definitions.Def_PCNonBool_Supplement_pcAxiomsCNF
import Definitions.Def_PCNonBool_Supplement_ProofSystemP
import Definitions.Def_PCNonBool_Supplement_Automatable

namespace PCNonBool.Supplement

/-- **Theorem 7.1** (Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, *On the Power of Polynomial Calculus over Non-Boolean Domains*, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), p.50 (PDF p.53)). There exists a polynomial-time algorithm `A` mapping
CNF formulas to CNF formulas such that, for every `n`-variable CNF formula `F`:
1. If `F` is satisfiable, then `A(F)` is unsatisfiable and has a polynomial calculus refutation of
   size `poly(|F|)`.
2. If `F` is unsatisfiable, then every `P`-refutation of `A(F)` requires size at least
   `exp(Ω(n²))`.
In particular, if `P` is automatable then `P = NP`.

Here `P` is PCR supplied with `{±1}`-variables over a field `F` with `char F ≠ 2`, and `|F|` is the
number of clauses.

**Formalization Note** `A` is computed by a Mathlib two-stack Turing machine in polynomial time
(`TM2ComputableInPolyTime`) on the binary encoding `encodeCNF`. `poly(|F|)` is `C(|F| + 1)^d` and
`exp(Ω(n²))` is `exp(ε n²)`, with the constants `C, d, ε` chosen after `A` and before the field and
the formula. Part 1's refutation is plain polynomial calculus over `{0, 1}`-valued variables with
no reduction (`red = id`, p.11); part 2's are `P`-refutations with lines in reduced form (`redP`).
`P = NP` is read as `SATinP`, and "automatable" is `IsAutomatable F`. -/
theorem theorem_7_1 :
    ∃ A : CNF → CNF, Nonempty (Turing.TM2ComputableInPolyTime encodeCNF encodeCNF A) ∧
    ∃ (C d : ℕ) (ε : ℝ), 0 < ε ∧
    ∀ (F : Type) [Field F], ringChar F ≠ 2 →
      (∀ Φ : CNF, Satisfiable Φ →
        ¬ Satisfiable (A Φ) ∧
        ∃ π : List (MvPolynomial ℕ F),
          PCNonBool.IsRefutation LinearMap.id (pcAxiomsCNF F (A Φ)) π ∧
          PCNonBool.pcSize π ≤ C * (Φ.length + 1) ^ d) ∧
      (∀ Φ : CNF, ¬ Satisfiable Φ →
        ∀ π : List (MvPolynomial PVar F), PCNonBool.IsRefutation redP (PAxioms F (A Φ)) π →
          Real.exp (ε * (Φ.numVars : ℝ) ^ 2) ≤ (PCNonBool.pcSize π : ℝ)) ∧
      (IsAutomatable F → SATinP) := by sorry

end PCNonBool.Supplement
