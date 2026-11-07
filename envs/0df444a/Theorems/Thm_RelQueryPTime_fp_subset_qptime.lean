-- Prove2me | Theorems.Thm_RelQueryPTime_fp_subset_qptime
-- name    : RelQueryPTime.fp_subset_qptime
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:42:01.068744+00:00
-- url     : https://prove2.me/theorems/bacc6be3-fcd0-402e-9f83-4526db4d1351
-- title:
--   §2 — $\mathrm{FP} \subseteq \mathrm{QPTIME}$ on ordered databases
-- statement:
--   Every query expressible in relational calculus with $\le$ and the least fixpoint operator is computable in polynomial time: for every scheme $\sigma$ and every arity $r$,
--   $$
--   \mathrm{FP}(\le) \subseteq \mathrm{Q}(\le)\mathrm{PTIME}.
--   $$
--   Here a query in $\mathrm{FP}(\le)$ is defined by a well-formed formula in which LFP may occur anywhere, nested and with parameters, and $r = 0$ (Boolean queries) is included.
--
--   This is the easy half of Theorem 1, obtained from Proposition 1 by evaluating the fixpoints from the inside out.
--
--   Differences from the source:
--   - generalization: FP, the Fixpoint Hierarchy of Chandra and Harel (alternations of quantification and LFP) → FP(≤) with LFP anywhere in a formula, nested and with parameters, and every arity r including 0; reason: every level of the hierarchy is such a formula, so the page's inclusion is the special case
--   - encoding: ordered database with domain D and a total order ≤; computation on a database → domain Fin n with its natural order; input ⟨B,c⟩ = 1ⁿ0, the bit tables, one-hot c_i; Cook's one-tape machines; reason: every finite total order is uniquely isomorphic to Fin n with its order; the page fixes no machine model; 1ⁿ0 replaces the table of ≤, which n determines
-- source:
--   N. Immerman, Relational Queries Computable in Polynomial Time (Extended Abstract), Proc. 14th ACM STOC, 1982, pp.147–152, doi:10.1145/800070.802187, §2, p.149 ("We have already seen in Proposition 1 that Σω is contained in QPTIME. It follows that FP ⊆ QPTIME.") (PDF p.3)

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_RelQueryPTime_Syntax
import Definitions.Def_RelQueryPTime_Encoding
import Definitions.Def_RelQueryPTime_Classes

namespace RelQueryPTime

/-- `FP ⊆ QPTIME` (Immerman, *Relational Queries Computable in Polynomial Time*, STOC 1982, §2, p.149: "We have already seen in Proposition 1 that `Σ_ω` is contained in
QPTIME. It follows that FP ⊆ QPTIME."): every query expressible in relational calculus with `≤`
and the least fixpoint operator is computable in polynomial time on ordered databases.

**Formalization Note** `FP` here allows `LFP` anywhere in a formula, nested and with parameters,
and every arity `r`, including Boolean queries (`r = 0`). -/
theorem fp_subset_qptime (σ : Schema) (r : ℕ) : FP σ r ⊆ QPTIME σ r := by sorry

end RelQueryPTime
