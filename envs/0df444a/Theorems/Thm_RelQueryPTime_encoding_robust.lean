-- Prove2me | Theorems.Thm_RelQueryPTime_encoding_robust
-- name    : RelQueryPTime.encoding_robust
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:42:24.34451+00:00
-- url     : https://prove2.me/theorems/bbc099ea-e73c-4957-91d2-c86c07cef332
-- title:
--   Proof of Theorem 1 — one-hot and positional binary constants give the same $\mathrm{P}$
-- statement:
--   For every scheme $\sigma$, arity $r$ and $r$-ary query $Q$ on ordered databases,
--   $$
--   \mathrm{Graph}(Q) \in \mathrm{P} \iff \mathrm{GraphBin}(Q) \in \mathrm{P},
--   $$
--   where $\mathrm{Graph}$ writes each constant $c_i$ as an $n$-bit one-hot vector and $\mathrm{GraphBin}$ writes it in positional binary with $\lceil \log_2(n+1)\rceil$ bits; both encodings start with $1^n0$ followed by the bit tables of the relations.
--
--   So the class $\mathrm{Q}(\le)\mathrm{PTIME}$ does not depend on which binary representation of $c_1,\dots,c_r$ is chosen. The page leaves that choice open.
--
--   Differences from the source:
--   - reading: some binary representation for c1…cr → the equivalence of the one-hot and the positional-binary representations for membership in P; reason: the mission's encoding uses one-hot; this statement shows the choice does not change Q(≤)PTIME
-- source:
--   N. Immerman, Relational Queries Computable in Polynomial Time (Extended Abstract), Proc. 14th ACM STOC, 1982, pp.147–152, doi:10.1145/800070.802187, proof of Theorem 1, p.149 ("followed by some binary representation for c1…cr") (PDF p.3)

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_RelQueryPTime_Syntax
import Definitions.Def_RelQueryPTime_Encoding
import Definitions.Def_RelQueryPTime_EncodingBin

namespace RelQueryPTime

/-- The encoding of the constants does not matter (Immerman, *Relational Queries Computable in Polynomial Time*, STOC 1982, proof of Theorem 1, p.149: "followed by
some binary representation for `c₁…c_r`"): for every query `Q`, `Graph(Q)` is in `P` under the
one-hot encoding of `c₁, …, c_r` used throughout this mission (`enc`) iff it is in `P` under
positional binary (`encBin`). -/
theorem encoding_robust (σ : Schema) (r : ℕ) (Q : Query σ r) :
    Graph Q ∈ CookPvsNP.P Bool ↔ GraphBin Q ∈ CookPvsNP.P Bool := by sorry

end RelQueryPTime
