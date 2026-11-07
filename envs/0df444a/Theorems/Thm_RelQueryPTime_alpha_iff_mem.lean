-- Prove2me | Theorems.Thm_RelQueryPTime_alpha_iff_mem
-- name    : RelQueryPTime.alpha_iff_mem
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:42:10.586104+00:00
-- url     : https://prove2.me/theorems/8e2eda1b-e881-4643-b8ce-fd2856ebf5ee
-- title:
--   Proof of Theorem 1 — $\mathrm{Q}(\le)\mathrm{PTIME} \subseteq \Sigma_\omega(\le)$ for queries with free variables (corrected: $r \ge 1$)
-- statement:
--   For every scheme $\sigma$ and every arity $r \ge 1$, every query computable in polynomial time on ordered databases lies in the positive form of $\Sigma_\omega(\le)$:
--   $$
--   \mathrm{Q}(\le)\mathrm{PTIME} \subseteq \Sigma_\omega^{+}(\le).
--   $$
--   That is, for every set $S$ of pairs $\langle B, \bar c\rangle$ accepted by a polynomial-time Turing machine there is $\alpha(\bar x) = \mathrm{LFP}(\varphi)(\bar v)$, with $\varphi$ first order, in some $\Sigma_\alpha$, and positive in its relation variable, such that $B \models \alpha(\bar c) \iff \langle B,\bar c\rangle \in S$ for all ordered databases $B$ of every size.
--
--   This is the hard half of Theorem 1.
--
--   Differences from the source:
--   - correction: Q(≤)PTIME ⊆ Σω(≤) for every arity → for arity r ≥ 1 (Boolean queries are handled in Theorem 1 through one dummy variable); reason: for r = 0 the substituted tuple v is empty, so LFP(φ)() is the first-order sentence φ(∅) (proved in the sanity file); counterexample: on the scheme with only ≤, the Boolean query 'the domain has even size' is in Q(≤)PTIME but is not first order on linear orders (Ehrenfeucht–Fraïssé), hence not in the literal Σω
--   - reading: φ monotone → the relation variable occurs only positively; reason: positivity implies monotonicity, so this is the stronger conclusion; the page's Ψ is positive
--   - reading: some binary representation for c1…cr → one-hot c_i; reason: under positional binary the first-order M0 of the proof does not exist; milestone encoding_robust shows that P is unchanged
--   - encoding: ordered database with domain D and a total order ≤; computation on a database → domain Fin n with its natural order; input ⟨B,c⟩ = 1ⁿ0, the bit tables, one-hot c_i; Cook's one-tape machines; reason: every finite total order is uniquely isomorphic to Fin n with its order; the page fixes no machine model; 1ⁿ0 replaces the table of ≤, which n determines
-- source:
--   N. Immerman, Relational Queries Computable in Polynomial Time (Extended Abstract), Proc. 14th ACM STOC, 1982, pp.147–152, doi:10.1145/800070.802187, proof of Theorem 1, p.149 ("Let S = {<B1,c1> . . . } be a set of pairs … We must show that there is a query α(x1…xr) ∈ Σω which expresses S"; "Thus, as desired, B ⊨ α(c) ↔ <B,c> ∈ S.") (PDF p.3)

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_RelQueryPTime_Syntax
import Definitions.Def_RelQueryPTime_Encoding
import Definitions.Def_RelQueryPTime_Classes

namespace RelQueryPTime

/-- `Q(≤)PTIME ⊆ Σ_ω(≤)` for queries with at least one free variable (Immerman, *Relational Queries Computable in Polynomial Time*, STOC 1982, proof of Theorem 1,
p.149: "Thus, as desired, `B ⊨ α(c) ↔ <B,c> ∈ S`."): every polynomial-time query `S` of arity
`r ≥ 1` on ordered databases is `α(x) = LFP(φ)(v)` for a first-order `φ ∈ Σ_α` in which the
relation variable occurs only positively.

**Formalization Note** It holds on databases of every size, `n = 1` included (the page's
construction needs two distinct elements); `n = 0` is vacuous for `r ≥ 1`. -/
theorem alpha_iff_mem (σ : Schema) (r : ℕ) (hr : 0 < r) : QPTIME σ r ⊆ SigmaOmegaPos σ r := by sorry

end RelQueryPTime
