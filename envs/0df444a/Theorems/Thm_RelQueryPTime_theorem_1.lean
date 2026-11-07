-- Prove2me | Theorems.Thm_RelQueryPTime_theorem_1
-- name    : RelQueryPTime.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:42:12.341458+00:00
-- url     : https://prove2.me/theorems/e8c0a309-60ee-4cff-9d41-789d096d7791
-- title:
--   Theorem 1 — on ordered databases $\mathrm{FP}(\le) = \Sigma_\omega(\le) = \mathrm{Q}(\le)\mathrm{PTIME}$ (corrected: Boolean queries enter $\Sigma_\omega$ through one dummy variable)
-- statement:
--   On ordered databases, relational calculus with the least fixpoint operator expresses exactly the polynomial-time queries, and one application of LFP suffices. For every relational scheme $\sigma$:
--
--   1. for every arity $r \ge 0$,
--   $$
--   \mathrm{FP}(\le) = \mathrm{Q}(\le)\mathrm{PTIME};
--   $$
--   2. for every arity $r \ge 1$,
--   $$
--   \Sigma_\omega(\le) = \mathrm{Q}(\le)\mathrm{PTIME} = \Sigma_\omega^{+}(\le),
--   $$
--   where $\Sigma_\omega$ reads "monotone" semantically and $\Sigma_\omega^{+}$ requires the relation variable to occur only positively;
--   3. a Boolean query $Q$ ($r = 0$) is in $\mathrm{Q}(\le)\mathrm{PTIME}$ iff $Q$, read as a unary query with one dummy free variable, is in $\Sigma_\omega(\le)$, iff it is in $\Sigma_\omega^{+}(\le)$.
--
--   Here an ordered database has domain $\{0,\dots,n-1\}$ with its natural order ($n = 0$ allowed), $\mathrm{Q}(\le)\mathrm{PTIME}$ is defined by $\mathrm{Graph}(Q) \in \mathrm{P}$ for Cook's Turing machines, and $\mathrm{FP}(\le)$ allows LFP anywhere in a formula.
--
--   The theorem is a syntactic characterization of polynomial time on ordered structures. It was found independently by Vardi.
--
--   Differences from the source:
--   - correction: Q(≤)PTIME = Σω(≤) for queries of every arity → for arity r ≥ 1; a Boolean query is in Q(≤)PTIME iff it is in Σω with one dummy free variable; reason: for r = 0 the substituted tuple v is empty and LFP(φ)() is the first-order sentence φ(∅); counterexample satisfying every assumption of the page: on the scheme with only ≤, 'the domain has even size' is in Q(≤)PTIME (and in FP(≤)) but is not first order on linear orders (Ehrenfeucht–Fraïssé), so not in the literal Σω
--   - reading: some binary representation for c1…cr → one-hot c_i in the input ⟨B,c⟩; reason: under positional binary the first-order M0 of the proof does not exist; milestone encoding_robust shows P is unchanged
--   - reading: φ monotone (p.148, semantic) → both readings: semantic monotonicity on every database (SigmaOmega) and positive occurrence (SigmaOmegaPos), each equal to Q(≤)PTIME; reason: neither reading is the weaker one; both equalities are stated
--   - encoding: ordered database with a total order ≤ on the domain; the input contains ⟨B,c⟩ → domain Fin n with its natural order; input 1ⁿ0, the bit tables, then the constants; P is Cook's class of one-tape machines halting within |w|^k + k; reason: every finite total order is uniquely isomorphic to Fin n; 1ⁿ0 replaces the table of ≤, which n determines, and is polynomial-time interconvertible with it; the page fixes no machine model
--   - generalization: FP(≤), the queries of relational calculus plus LFP; databases of the page → FP with LFP anywhere (nested, with parameters), arities a_i = 0 allowed, domain size n = 0 allowed; reason: each only enlarges what is covered; the page's languages and databases are instances
-- source:
--   N. Immerman, Relational Queries Computable in Polynomial Time (Extended Abstract), Proc. 14th ACM STOC, 1982, pp.147–152, doi:10.1145/800070.802187, Theorem 1, p.149 ("Q(≤)PTIME = Σω(≤)"); stated in words on p.147 ("Then the queries expressible in L are exactly the queries computable in polynomial time."); p.149 ("Q(≤)PTIME = FP(≤), and in fact only one application of LFP is needed") (PDF pp.1, 3)

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_RelQueryPTime_Syntax
import Definitions.Def_RelQueryPTime_Encoding
import Definitions.Def_RelQueryPTime_Classes

namespace RelQueryPTime

/-- Theorem 1 (Immerman, *Relational Queries Computable in Polynomial Time*, STOC 1982, p.149, "`Q(≤)PTIME = Σ_ω(≤)`"; in words p.147: "the queries expressible in L
are exactly the queries computable in polynomial time"; and p.149: "`Q(≤)PTIME = FP(≤)`, and in fact
only one application of LFP is needed"). On ordered databases of any scheme `σ`:
1. `FP(≤) = Q(≤)PTIME` for queries of every arity `r`;
2. `Σ_ω(≤) = Q(≤)PTIME` for every arity `r ≥ 1`, with "monotone" read semantically and read as
   "the relation variable occurs only positively";
3. a Boolean query (`r = 0`) is in `Q(≤)PTIME` iff, read with one dummy free variable, it is in
   `Σ_ω(≤)` (in either reading).

**Formalization Note** The literal `Σ_ω` has no Boolean queries beyond first-order sentences (a
`0`-ary `LFP` is its body at the empty relation), so for `r = 0` the equality with `Σ_ω` is stated
through `liftBool`. -/
theorem theorem_1 (σ : Schema) :
    (∀ r, FP σ r = QPTIME σ r) ∧
    (∀ r, 0 < r → SigmaOmega σ r = QPTIME σ r ∧ SigmaOmegaPos σ r = QPTIME σ r) ∧
    (∀ Q : Query σ 0, (Q ∈ QPTIME σ 0 ↔ liftBool Q ∈ SigmaOmega σ 1) ∧
      (Q ∈ QPTIME σ 0 ↔ liftBool Q ∈ SigmaOmegaPos σ 1)) := by sorry

end RelQueryPTime
