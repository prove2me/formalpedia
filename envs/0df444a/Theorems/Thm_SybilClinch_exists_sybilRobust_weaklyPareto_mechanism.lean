-- Prove2me | Theorems.Thm_SybilClinch_exists_sybilRobust_weaklyPareto_mechanism
-- name    : SybilClinch.exists_sybilRobust_weaklyPareto_mechanism
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:42:15.719369+00:00
-- url     : https://prove2.me/theorems/4931d510-1a32-453b-8c11-690b117cf59b
-- title:
--   Theorem 1.1 — an IR, exactly settling, Sybil-robust IC and weakly Pareto optimal AMM mechanism exists
-- statement:
--   Assume that a strategic trader cannot over-report its budget in aggregate across the Sybil identities it submits in its own trading direction. Then for every admissible AMM $\varphi$ there exists an AMM mechanism $\mathcal M$, mapping every finite profile of reported orders (sell-$Y$ orders $(v_i,q_i)$ and sell-$X$ orders $(u_i,r_i)$) to an outcome, such that on every profile of finite nonnegative reports:
--
--   1. the outcome is exact-settlement feasible (Definition 2.2): it respects every identity's budget, and the net pool flows end on the reserve curve;
--   2. the outcome is individually rational (Definition 2.3) when every report is its trader's true type;
--   3. the outcome is weakly Pareto optimal for eligible bids (Definition 2.7, both clauses);
--
--   and $\mathcal M$ is Sybil-robust incentive compatible (Definition 2.6): for every true type of either direction (eligible or not), every fixed profile of the other traders and every admissible two-sided Sybil strategy (Definition 2.4), truthful merged reporting gives at least the true utility (5)–(6) of the deviation.
--
--   The budget assumption is exactly the strategy space of Definition 2.4. Theorem 1.2 of the paper shows it cannot be dropped.
--
--   Differences from the source:
--   - encoding: an AMM mechanism mapping the reported orders (an unordered batch) to an outcome → a function from a finite set of natural-number identity labels and a report function to an outcome per label; Sybil-robust IC quantifies over every fresh label and over report functions that agree on the others' identities; reason: labels carry no information the mechanism can exploit in the incentive condition; the properties are required on every profile
--   - encoding: the budget assumption of the theorem → StratAdmissible (Definition 2.4) as the deviation space of SybilRobustIC; reason: the assumption is the strategy space of Definition 2.4
-- source:
--   Zhang, Li, Shi, Zhang, Xia, Han, Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design, arXiv:2610.36629 (held copy sha256 93c5d05b…), §1, Theorem 1.1, p.3 (PDF p.5)

import Mathlib
import Definitions.Def_SybilClinch_ExactSettle
import Definitions.Def_SybilClinch_IndivRational
import Definitions.Def_SybilClinch_WeakPO
import Definitions.Def_SybilClinch_SybilRobustIC

set_option autoImplicit false

open Filter Topology Set MeasureTheory

namespace SybilClinch

/-- Zhang, Li, Shi, Zhang, Xia, Han, *Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design*, arXiv:2610.36629 (held copy sha256 93c5d05b…), §1, Theorem 1.1 (Sybil-robust and weakly Pareto optimal AMM), printed p.3 (PDF p.5).

Assume that a strategic trader cannot over-report its budget in aggregate across the Sybil
identities it submits in its own trading direction. Then for every admissible AMM there exists an
AMM mechanism that is individually rational, exactly settles against the pool, and satisfies
Sybil-robust incentive compatibility and weak Pareto optimality for eligible bids.

**Formalization Note.** A mechanism maps a finite set of identity labels with reports to an outcome
per identity. Exact settlement (Definition 2.2), individual rationality (Definition 2.3, the profile
read as truthful) and weak Pareto optimality (Definition 2.7, both clauses) are required on every
profile of finite nonnegative reports; Sybil-robust incentive compatibility is Definition 2.6 over
the strategy space of Definition 2.4, which encodes the budget assumption. -/
theorem exists_sybilRobust_weaklyPareto_mechanism (A : AdmissibleAMM) :
    ∃ Mech : Finset ℕ → (ℕ → Report) → ℕ → Fill,
      (∀ (ids : Finset ℕ) (rep : ℕ → Report), (∀ i ∈ ids, (rep i).Valid) →
        ExactSettle A ids rep (Mech ids rep) ∧ IndivRational ids rep (Mech ids rep) ∧
          WeakPO A ids rep (Mech ids rep)) ∧
      SybilRobustIC (fun ids rep f => f = Mech ids rep) := by sorry

end SybilClinch
