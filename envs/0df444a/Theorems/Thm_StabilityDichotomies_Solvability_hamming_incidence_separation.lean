-- Prove2me | Theorems.Thm_StabilityDichotomies_Solvability_hamming_incidence_separation
-- name    : StabilityDichotomies.Solvability.hamming_incidence_separation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:05:32.461422+00:00
-- url     : https://prove2.me/theorems/d1a096de-6c8a-4b36-89f8-56c4b4990e54
-- title:
--   Corollary 3.5 — Hamming separation by incidence distance
-- statement:
--   Let $I=(V,C)$ be minimally unsatisfiable over $\Gamma$, and let $c,c'$ be distinct constraint occurrences. For every $x\in\operatorname{Sol}(I-c)$ and $y\in\operatorname{Sol}(I-c')$,
--
--   $$d_H(x,y)\ge\tfrac12 d_{G_{\rm inc}(I)}(c,c').$$
--
--   The Hamming distance counts variables, with no division by $|V|$. This forces solutions of distant deletions apart and is used for the solver-law lower bound.
--
--   **Formalization Note** The equivalent inequality $d_G(c,c')\le2d_H(x,y)$ is stated in extended natural numbers. It also forces the graph distance to be finite, as guaranteed by Lemma 3.4; an unreachable-pair default of zero cannot make this statement trivial.
--
--   Differences from the source:
--   - encoding: finite Boolean variable sets and multiset constraints → arbitrary finite types, Bool, Fin arity coordinates, and Multiset constraints; reason: bijections preserve all assignments and constraints, while retaining repeated scopes and occurrence multiplicities
--   - encoding: distinct constraint occurrences c and c′ → distinct positions in a chosen representative list of the constraint multiset, used only in the incidence graph; reason: each position is one occurrence; this order is absent from solver inputs, and changing representatives gives an isomorphic graph
--   - encoding: d_H(x,y) ≥ (1/2) d_G(c,c′) → extended natural distance d_G(c,c′) ≤ 2 d_H(x,y); reason: distances are integer counts, and Lemma 3.4 guarantees reachability under exactly the same hypotheses
--   - generalization: the introduction uses n≥2 for the number of variables → the path and separation statements also allow carriers of size zero or one; reason: the source arguments do not require n≥2; the empty case has no minimally unsatisfiable instance, and on one variable distinct deletion solutions disagree at that variable and are joined by a length-two incidence path
-- source:
--   Chunyang Wang, Yuichi Yoshida, Stability Dichotomies for Boolean Constraint Satisfaction Problems, STOC 2027 submission #535 (October 2026), p.12, Corollary 3.5; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf

import Definitions.Def_StabilityDichotomies_Solvability_Incidence

namespace StabilityDichotomies.Solvability

/-- Corollary 3.5, p.12. Extended distance is bounded by twice the Hamming count;
this also asserts reachability and cannot become vacuous through dist=0 on disconnection. -/
theorem hamming_incidence_separation (Γ : Language) (V : Type) [Fintype V]
    (I : Instance Γ V) (hI : MinimallyUnsatisfiable I)
    (c c' : Occurrence I) (hcc' : c ≠ c') (x y : V → Bool)
    (hx : Solution (I.delete (occurrenceConstraint I c)) x)
    (hy : Solution (I.delete (occurrenceConstraint I c')) y) :
    (incidenceGraph I).edist (.inr c) (.inr c') ≤
      ((2 * hammingDist x y : ℕ) : ℕ∞) := by sorry

end StabilityDichotomies.Solvability
