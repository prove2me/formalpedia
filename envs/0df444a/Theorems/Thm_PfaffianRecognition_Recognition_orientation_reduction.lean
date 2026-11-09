-- Prove2me | Theorems.Thm_PfaffianRecognition_Recognition_orientation_reduction
-- name    : PfaffianRecognition.Recognition.orientation_reduction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T04:41:27.863385+00:00
-- url     : https://prove2.me/theorems/58f1b4f3-3b8a-45fd-9773-162c44f3ac4b
-- title:
--   Lemma 3.3 — polynomial-time orientation construction
-- statement:
--   There is one deterministic polynomial-time algorithm that works for every finite simple graph $G$ with a perfect matching. It outputs an orientation $D^\star$ of $G$ such that
--   $$
--   G\text{ admits a Pfaffian orientation}\iff D^\star\text{ is Pfaffian}.
--   $$
--   The output orientation need not be Pfaffian when $G$ is not Pfaffian. The same algorithm and the same polynomial bound apply to every input graph. This is the orientation-construction result attributed in the source to Vazirani and Yannakakis, and reduces graph recognition to testing a specified orientation.
--
--   **Formalization Note** The conclusion includes a finite-alphabet deterministic machine, constants $C\ge1,k\in\mathbb N$, actual execution within $C(L+2)^k$ steps for input length $L$, and its correct direction-table output. Neither its correctness nor an implementation of matching is a hypothesis. The empty graph is included.
--
--   Differences from the source:
--   - encoding: finite simple ordered graphs with labels 1 through N → SimpleGraph (Fin N), with source labels equal to Lean indices plus one; reason: order-preserving relabeling covers every finite simple graph
--   - encoding: a deterministic polynomial-time orientation constructor → one deterministic finite-alphabet bit machine outputs D star within C(L+2)^k steps, uniformly before all graphs; reason: actual execution and output encode the polynomial-time construction claim
-- source:
--   Priyanshu Pant, Ranveer Singh, Pfaffian Recognition is in coRP, STOC 2027 submission #858 (October 2026), Lemma 3.3, p. 8 (citing Vazirani–Yannakakis, Theorem 3.1); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/858.pdf

import Definitions.Def_PfaffianRecognition_Recognition_computation_model

namespace PfaffianRecognition.Recognition

/-- Lemma 3.3, p. 8. One deterministic polynomial bit-time constructor works for every
finite simple graph with a perfect matching, including the empty graph. -/
theorem orientation_reduction : HasPolyOrientationReduction := by sorry

end PfaffianRecognition.Recognition
