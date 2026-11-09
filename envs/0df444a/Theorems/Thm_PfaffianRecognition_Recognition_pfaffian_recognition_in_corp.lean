-- Prove2me | Theorems.Thm_PfaffianRecognition_Recognition_pfaffian_recognition_in_corp
-- name    : PfaffianRecognition.Recognition.pfaffian_recognition_in_corp
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T04:41:22.967067+00:00
-- url     : https://prove2.me/theorems/3a1ecf24-16b2-4c5b-8ea4-8befe3a33cde
-- title:
--   Theorem 1.1 — Pfaffian recognition is in coRP
-- statement:
--   Pfaffian graph recognition belongs to coRP. There exists one randomized polynomial bit-time algorithm that decides, for every finite simple graph $G$, whether it admits a Pfaffian orientation, with
--   $$
--   G\text{ Pfaffian}\Longrightarrow\Pr[\mathrm{accept}]=1,\qquad
--   G\text{ non-Pfaffian}\Longrightarrow\Pr[\mathrm{reject}]\ge\tfrac12.
--   $$
--   Every execution halts within a uniform polynomial bound. All graph orders and all finite simple graphs are included: there is no matching-covered, connected, planar, bipartite, nonempty or even-order promise. This is the paper's headline theorem about existence of an orientation, beyond the test of a prescribed orientation.
--
--   **Formalization Note** The statement is membership of the graph-encoding language in the execution-based coRP predicate. Its single finite program and constants are existentially chosen before every string, and the polynomial dominates time and tape length. Perfect matchings and integer matching signs define mathematical Pfaffianity independently of the algorithm. Empty and no-perfect-matching graphs are Pfaffian under this definition.
--
--   Differences from the source:
--   - encoding: finite simple ordered graphs with labels 1 through N → SimpleGraph (Fin N), with source labels equal to Lean indices plus one; reason: order-preserving relabeling covers every finite simple graph
--   - encoding: a randomized polynomial-time algorithm → one finite-alphabet fair-bit machine with a uniform C(L+2)^k bound on actual steps and random tape, chosen before all input strings; reason: this is the usual polynomial bit-time meaning of coRP, with uniform finite counts of tapes
--   - encoding: a graph input → the published unary-header adjacency-bit encoding, with malformed strings outside the language; reason: every graph is encoded and invalid strings admit a deterministic polynomial parser
-- source:
--   Priyanshu Pant, Ranveer Singh, Pfaffian Recognition is in coRP, STOC 2027 submission #858 (October 2026), Theorem 1.1 and definition of coRP, p. 3; proof p. 8; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/858.pdf

import Definitions.Def_PfaffianRecognition_Recognition_computation_model

namespace PfaffianRecognition.Recognition

/-- Theorem 1.1, p. 3; proof p. 8. All finite simple graphs, one uniform polynomial
bit-time machine, perfect completeness and rejection probability at least 1/2. -/
theorem pfaffian_recognition_in_corp : InCoRP pfaffianLanguage := by sorry

end PfaffianRecognition.Recognition
