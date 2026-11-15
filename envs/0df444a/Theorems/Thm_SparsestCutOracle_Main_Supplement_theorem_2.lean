-- Prove2me | Theorems.Thm_SparsestCutOracle_Main_Supplement_theorem_2
-- name    : SparsestCutOracle.Main.Supplement.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T05:49:17.077236+00:00
-- url     : https://prove2.me/theorems/7d0dab47-78d6-4d12-ab96-f3657c78fd50
-- title:
--   Theorem 2 — Hierarchical congestion approximator construction
-- statement:
--   Let $G$ be a connected undirected graph on $n\ge2$ vertices with $m$ listed edges, real capacities at least one, and total capacity $W$. There are universal positive constants $c_1,c_2,C_q$ such that, for every natural failure exponent $a$, one randomized charged program and constants $C_t>0,c\in\mathbb N$, fixed before the instance, work for every real $\kappa\in[c_1/\ln n,c_2]$. The program computes a complete hierarchical congestion approximator of quality
--   $$
--   C_q\ell\ell_2\sqrt{\ell/\kappa},\qquad \ell=1+\ln n,\quad\ell_2=1+\ln(1+\ln n),
--   $$
--   with probability at least $1-n^{-a}$, and has expected charged work at most
--   $$
--   C_t(m+n^{1+\kappa})(1+\ln W)(1+\ln n)^c.
--   $$
--   Halting is almost sure and work is integrable. The program receives only the graph and $\kappa$, and computes the finite output hierarchy itself. This is the congestion-approximation application of the retained sparsest-cut goal; Theorem 9 supplies its hierarchy routing bound.
--
--   Differences from the source:
--   - reading: a randomized algorithm with the guarantees of §8.2 → one admissible published-machine program per failure exponent, correct on a measurable set of tapes of probability at least 1−n^(−a); reason: §8.2 uses high-probability subroutines; amplification is chosen uniformly before every input, as in the base mission
--   - encoding: O(log n log log n √(log n/κ)) quality and expected Õ((m+n^(1+κ)) log W) time → uniform positive constants C_q,C_t, natural exponent c, and positive logarithms ℓ=1+ln n, ℓ₂=1+ln(1+ln n), 1+ln W; reason: these have the printed asymptotic order and define meaningful finite-size bounds, including n=2 and W=1
--   - encoding: the graph G and real κ as in Theorem 1, with the connectedness convention on page 7 → connected loopless edge lists on Fin n with n≥2, nonnegative real capacities at least one, and no vertex-weight input; reason: the logarithmic κ range requires n≥2; graphInts and the existing capacity representation preserve parallel edges and all real capacities
--   - encoding: a computed hierarchical congestion approximator → finite height and n integer cluster labels per level, decoded into a complete hierarchy using per-cluster cut tests; reason: explicit output cells prevent free computation; cut tests follow Theorem 9’s proof as documented for that milestone
--   - reading: the congestion-approximator definition on page 44 uses the multilevel union boundary → per-cluster cut tests at every hierarchy level, as in the proof of Theorem 9; reason: the proof on page 45 uses these tests; the literal union-degree definition fails on the weighted-path counterexample in MODERATION_NOTES.md
-- source:
--   Robin Münk, Monika Henzinger, Harald Räcke, STOC 2027 submission #1170 (October 2026), p. 4, Theorem 2

import Mathlib
import Definitions.Def_SparsestCutOracle_Main_Supplement_Construction

namespace SparsestCutOracle.Main.Supplement

/-- Theorem 2, p.4: one uniformly chosen charged program constructs the full hierarchy,
with the stated quality/time tradeoff for every admissible real κ. -/
theorem theorem_2 : HierarchyConstruction := by sorry

end SparsestCutOracle.Main.Supplement
