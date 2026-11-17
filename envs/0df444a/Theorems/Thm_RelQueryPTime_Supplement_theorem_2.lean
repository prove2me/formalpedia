-- Prove2me | Theorems.Thm_RelQueryPTime_Supplement_theorem_2
-- name    : RelQueryPTime.Supplement.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:44:39.410594+00:00
-- url     : https://prove2.me/theorems/21326535-a6eb-4b7d-8299-2855873580c0
-- title:
--   Theorem 2 — without an ordering, $\mathrm{FP} = \Sigma_\omega$: the hierarchy collapses at the first fixpoint level (corrected: Boolean queries enter $\Sigma_\omega$ through one dummy variable)
-- statement:
--   Without an ordering of the domain, any query expressible with several (nested) applications of the least fixpoint operator can already be expressed with one. Let $\sigma$ be a relational scheme, and let all formulas be $\le$-free (no atom $x \le y$ anywhere, also inside nested $\mathrm{LFP}$ bodies). Then:
--
--   1. for every arity $r \ge 1$,
--   $$
--   \mathrm{FP} = \Sigma_\omega \quad\text{and}\quad \mathrm{FP} = \Sigma_\omega^{+},
--   $$
--   where $\Sigma_\omega$ reads "monotone" semantically and $\Sigma_\omega^{+}$ requires the relation variable to occur only positively;
--   2. a Boolean query $Q$ ($r = 0$) is in $\mathrm{FP}$ iff $Q$, read as a unary query with one dummy free variable, is in $\Sigma_\omega$, iff it is in $\Sigma_\omega^{+}$.
--
--   Here $\mathrm{FP}$ allows $\mathrm{LFP}$ anywhere in a formula (nested, with parameters, each body monotone), and $\Sigma_\omega$ consists of the queries $\mathrm{LFP}(\varphi)(\bar v)$ for a single first-order $\varphi \in \Sigma_\alpha$, $\alpha < \omega$. Databases have any finite size $n$, including $n = 0$ and $n = 1$.
--
--   This answers the question of Chandra and Harel whether the Fixpoint Hierarchy continues past $\Sigma_\omega$. On ordered databases the analogous collapse is part of Theorem 1, where both classes equal the polynomial-time queries; without an ordering no such machine characterization is available.
--
--   Differences from the source:
--   - correction: FP = Σω for queries of every arity → for arity r ≥ 1; a Boolean query is in FP iff it is in Σω with one dummy free variable; reason: for r = 0 the substituted tuple v is empty and LFP(φ)() is the first-order sentence φ(∅), so the literal Σω contains only first-order sentences, while 'the graph is connected' is a Boolean FP query (one LFP for reachability under a universal quantifier) that is not first order; the same correction as in RelQueryPTime.theorem_1
--   - reading: φ monotone (p.148, semantic) → both readings: semantic monotonicity on every database (SigmaOmegaU) and positive occurrence (SigmaOmegaPosU), each equal to FP; reason: neither reading is the weaker one; both equalities are stated
--   - encoding: databases without an ordering → databases on Fin n with formulas that contain no atom x ≤ y (Formula.NoLe); reason: a ≤-free formula cannot see the order of Fin n and every finite database is isomorphic to one on Fin n, so the instances are the same
--   - generalization: FP, the queries of relational calculus plus LFP, on the paper's databases → FP with LFP anywhere (nested, with parameters), arities a_i = 0 allowed, domain size n = 0 and n = 1 allowed; reason: each only enlarges what is covered, the paper's languages and databases are instances; the proof sketch's assumption that the domain has at least two elements (p.150) is a proof device, not a hypothesis of the theorem
-- source:
--   N. Immerman, Relational Queries Computable in Polynomial Time (Extended Abstract), Proc. 14th ACM STOC, 1982, pp.147–152, doi:10.1145/800070.802187, Theorem 2, p.149 ("FP = Σω"; "If we do not have an ordering … the hierarchy still collapses at the first fixpoint level"); stated in words on p.147 ("The Fixpoint Hierarchy collapses at the first fixpoint level"); proof sketch pp.149–151

import Mathlib
import Definitions.Def_RelQueryPTime_Syntax
import Definitions.Def_RelQueryPTime_Classes
import Definitions.Def_RelQueryPTime_Supplement_Unordered

namespace RelQueryPTime.Supplement

open RelQueryPTime

/-- Theorem 2 (Immerman, *Relational Queries Computable in Polynomial Time*, STOC 1982, §3, p.149:
"If we do not have an ordering … the hierarchy still collapses at the first fixpoint level:
Theorem 2: `FP = Σ_ω`"; in words p.147: "any query expressible with several applications of
least fixpoint can already be expressed with one"). Without an ordering (all formulas `≤`-free),
for every scheme `σ`:
1. for every arity `r ≥ 1`, `FP = Σ_ω`, with "monotone" read semantically (`SigmaOmegaU`) and
   read as "the relation variable occurs only positively" (`SigmaOmegaPosU`);
2. a Boolean query (`r = 0`) is in `FP` iff, read with one dummy free variable, it is in `Σ_ω`
   (in either reading).

**Formalization Note** "No ordering" means the formulas on both sides contain no atom `x ≤ y`
(`Formula.NoLe`), including inside nested `LFP` bodies. `FP` allows `LFP` anywhere. The literal
`Σ_ω` has no Boolean queries beyond first-order sentences (a `0`-ary `LFP` is its body at the
empty relation), so for `r = 0` the equality is stated through `liftBool`, as in
`RelQueryPTime.theorem_1`. Every domain size `n` is allowed, `n = 0` and `n = 1` included. -/
theorem theorem_2 (σ : Schema) :
    (∀ r, 0 < r → FPu σ r = SigmaOmegaU σ r ∧ FPu σ r = SigmaOmegaPosU σ r) ∧
    (∀ Q : Query σ 0, (Q ∈ FPu σ 0 ↔ liftBool Q ∈ SigmaOmegaU σ 1) ∧
      (Q ∈ FPu σ 0 ↔ liftBool Q ∈ SigmaOmegaPosU σ 1)) := by sorry

end RelQueryPTime.Supplement
