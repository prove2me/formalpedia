-- Prove2me | Theorems.Thm_PfaffianRecognition_Recognition_orientation_test
-- name    : PfaffianRecognition.Recognition.orientation_test
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T04:41:07.356189+00:00
-- url     : https://prove2.me/theorems/9a9e793a-76b6-4082-ae86-3d0304bca640
-- title:
--   Theorem 3.2 — one-sided randomized Pfaffian orientation test
-- statement:
--   There is one randomized polynomial-time algorithm for every finite simple graph $G$ and every orientation $D$ of it. It has perfect completeness and one-sided error:
--   $$
--   D\text{ Pfaffian}\Longrightarrow\Pr[\mathrm{accept}]=1,\qquad
--   D\text{ non-Pfaffian}\Longrightarrow\Pr[\mathrm{reject}]\ge\tfrac12.
--   $$
--   This includes empty graphs, graphs without perfect matchings, disconnected graphs and odd vertex counts. It tests the given orientation, as distinct from deciding the existence of any Pfaffian orientation.
--
--   **Formalization Note** The language is the set of valid graph/orientation encodings with Pfaffian orientation. A single finite program and uniform polynomial bound precede every input. Every fair tape halts with one bit; the probability is its exact finite counting probability. There is no nonsingularity or field-size assumption in the statement.
--
--   Differences from the source:
--   - encoding: finite simple ordered graphs with labels 1 through N → SimpleGraph (Fin N), with source labels equal to Lean indices plus one; reason: order-preserving relabeling covers every finite simple graph
--   - encoding: a randomized polynomial-time algorithm → one finite-alphabet fair-bit machine with a uniform C(L+2)^k bound on actual steps and random tape, chosen before all input strings; reason: this is the usual polynomial bit-time meaning of coRP, with uniform finite counts of tapes
--   - encoding: a graph and an orientation input → the graph encoding followed by N squared direction bits, with malformed pairs outside the language; reason: every valid pair is encoded and invalid strings admit a deterministic polynomial parser
-- source:
--   Priyanshu Pant, Ranveer Singh, Pfaffian Recognition is in coRP, STOC 2027 submission #858 (October 2026), Theorem 3.2, p. 7; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/858.pdf

import Definitions.Def_PfaffianRecognition_Recognition_computation_model

namespace PfaffianRecognition.Recognition

/-- Theorem 3.2, p. 7. Uniform randomized polynomial bit time, perfect completeness and
rejection probability at least 1/2; graph/orientation parsing is included. -/
theorem orientation_test : InCoRP pfaffianOrientationLanguage := by sorry

end PfaffianRecognition.Recognition
