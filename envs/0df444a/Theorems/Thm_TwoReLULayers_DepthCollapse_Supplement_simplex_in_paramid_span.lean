-- Prove2me | Theorems.Thm_TwoReLULayers_DepthCollapse_Supplement_simplex_in_paramid_span
-- name    : TwoReLULayers.DepthCollapse.Supplement.simplex_in_paramid_span
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T22:30:21.334731+00:00
-- url     : https://prove2.me/theorems/fa961443-3ab8-4b03-8bb4-e27618244932
-- title:
--   Theorem 14 — Rational simplex membership in the paramid span
-- statement:
--   For each $n\ge3$, let $\Delta^n=\operatorname{conv}(0,e_1,\ldots,e_n)$ in $\mathbb Q^n$, with the standard orientation. Its class satisfies
--   $$[\Delta^n]\in\Lambda_n^n\subseteq P_n^n.$$
--   The space $P_n^n$ is the geometric rational virtual-polytope quotient by translations and lower-dimensional polytopes. The subspace $\Lambda_n^n$ is the rational linear span of all rational $n$-dimensional paramids, with arbitrary rational apex, base translation and independent edge directions. This is rational quotient membership, rather than a real span identity or only existence of a network. No coning preimage is assumed. It is the companion theorem supplied by the paper's homological proof.
--
--   Differences from the source:
--   - encoding: Rational polytopes in oriented subspaces, with Minkowski differences modulo translations and lower-dimensional terms → Finite rational vertex and ordered-frame presentation of the same geometric quotient; reason: The presentation imposes exactly those geometric relations; facet boundaries are evaluated on a chosen representative, with no extra hypothesis
--   - encoding: n ≥ 3 → n = m+3, m : ℕ; reason: Equivalent enumeration of every permitted natural dimension or degree; avoids dependent transports from natural subtraction
-- source:
--   Kilian Rueß, Florestan Brunck, Christoph Hertrich, Jack Stade, Amir Yehudayoff, Two ReLU layers is all you need, STOC 2027 submission #980 (October 2026). Use this pinned PDF and its own labels; no arXiv version is asserted. p. 19, Theorem 14.

import Definitions.Def_TwoReLULayers_DepthCollapse_Supplement_Realization

namespace TwoReLULayers.DepthCollapse.Supplement

/-- Theorem 14, p.19. Every ambient dimension n+3≥3, over ℚ in the actual
geometric quotient. No coning preimage is assumed. -/
theorem simplex_in_paramid_span (n : ℕ) :
    simplexClass (n + 3) ∈ Lambda (n + 3) (n + 3) := by sorry

end TwoReLULayers.DepthCollapse.Supplement
