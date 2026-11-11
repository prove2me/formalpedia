-- Prove2me | Theorems.Thm_PlanarDFVS_SingleExp_protected_bimodal_solver
-- name    : PlanarDFVS.SingleExp.protected_bimodal_solver
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:08:41.673758+00:00
-- url     : https://prove2.me/theorems/daa913e7-d763-48f4-8ecd-73d0e11a0c71
-- title:
--   Lemma 3.6 (corrected: report infeasibility) — protected optimizer
-- statement:
--   Let $D$ be a loopless plane digraph and let $P$ contain every positive vertex, where $w(v)=b(v)-1$. One uniform polynomial-time algorithm returns a smallest DFVS disjoint from $P$, if one exists, and reports infeasibility otherwise:
--
--   $$\min\{|X|:D-X\text{ acyclic},\ X\cap P=\varnothing\}.$$
--
--   No feasibility hypothesis excludes an impossible protected instance. In a directed triangle with $P=V$, every vertex has $b(v)=1$, so the hypotheses hold but no protected-avoiding DFVS exists. This is the required correction of the printed existence claim.
--
--   The plane input uses directed support plus the inherited rotation restricted to one representative of each parallel class, and the protected mask. This retains the answer on every original instance and cannot create a new positive vertex. The degree and positive time coefficient are fixed before every graph, embedding and protected set. The minimum is attained by the returned set; no empty-family infimum is used.
--
--   Differences from the source:
--   - correction: unconditionally compute a minimum P-avoiding DFVS → return an attained minimum when feasible and report infeasibility otherwise; reason: the directed triangle with P=V is loopless and plane, has b=1 and no positive vertices, yet its only P-avoiding set is empty and is not a DFVS
--   - reading: From now on all digraphs are loopless (Observation 2.1) → Loopless G is explicit in the protected guarantee; reason: inherited standing assumption; the global algorithms preprocess all loops
--   - encoding: crossing-free plane embedding and its cyclic incidence orders → continuous crossing-free curves with locally straight endpoint germs and ray-ordered rotations; reason: local straightening realizes every finite topological embedding with the same rotations and facial walks; no Euler or target inequality is assumed
--   - reading: plane multigraph input with unspecified representation and n-polynomial time → canonical support and its inherited restricted rotation, plus P, encoded independently of duplicate multiplicity; reason: cycles are unchanged and deleting incidences cannot increase b; all originally positive vertices are protected, so every original instance remains covered
--   - reading: algorithms and polynomial factors with elementary operations and serialization unspecified → one finite binary instruction program, charged bit operations, fixed positive coefficients and natural degrees before every input; reason: retains uniform asymptotic resources with an operational program; no cost certificate or assumed fast optimizer
-- source:
--   Daniel Lokshtanov, Saket Saurabh, Jie Xue, STOC 2027 submission #1569 (October 2026), p. 7 (PDF p. 7), Lemma 3.6

import Mathlib
import Definitions.Def_PlanarDFVS_SingleExp_Interfaces

open scoped BigOperators
open Classical

namespace PlanarDFVS.SingleExp

/-- Corrected: on the directed triangle, protecting every vertex satisfies the
    printed hypotheses but leaves no feasible set. Report infeasibility. -/
theorem protected_bimodal_solver :
    ∃ (A : Program) (C : ℝ) (d : ℕ), 0 < C ∧ ProtectedGuarantee A C d := by sorry

end PlanarDFVS.SingleExp
