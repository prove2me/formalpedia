-- Prove2me | Theorems.Thm_StabilityDichotomies_Solvability_disagreement_along_path
-- name    : StabilityDichotomies.Solvability.disagreement_along_path
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:05:15.007395+00:00
-- url     : https://prove2.me/theorems/ba17f62a-7e02-4309-93c7-30afcd6b1dd3
-- title:
--   Lemma 3.4 — disagreement along a path
-- statement:
--   Let $I=(V,C)$ be a minimally unsatisfiable Boolean instance over $\Gamma$, and let $c,c'$ be distinct constraint occurrences. For every $x\in\operatorname{Sol}(I-c)$ and $y\in\operatorname{Sol}(I-c')$, there exists a simple incidence-graph path $P$ from $c$ to $c'$ such that
--
--   $$\forall v\in V,\quad v\in P\ \Longrightarrow\ x(v)\ne y(v).$$
--
--   Only the variable vertices are required to lie in the disagreement set. Connectivity and the path are conclusions, with no reachability hypothesis. This is the source's link between deletion solutions and graph geometry.
--
--   Differences from the source:
--   - encoding: finite Boolean variable sets and multiset constraints → arbitrary finite types, Bool, Fin arity coordinates, and Multiset constraints; reason: bijections preserve all assignments and constraints, while retaining repeated scopes and occurrence multiplicities
--   - encoding: distinct constraint occurrences c and c′ → distinct positions in a chosen representative list of the constraint multiset, used only in the incidence graph; reason: each position is one occurrence; this order is absent from solver inputs, and changing representatives gives an isomorphic graph
--   - generalization: the introduction uses n≥2 for the number of variables → the path and separation statements also allow carriers of size zero or one; reason: the source arguments do not require n≥2; the empty case has no minimally unsatisfiable instance, and on one variable distinct deletion solutions disagree at that variable and are joined by a length-two incidence path
-- source:
--   Chunyang Wang, Yuichi Yoshida, Stability Dichotomies for Boolean Constraint Satisfaction Problems, STOC 2027 submission #535 (October 2026), p.12, Lemma 3.4; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf

import Definitions.Def_StabilityDichotomies_Solvability_Incidence

namespace StabilityDichotomies.Solvability

/-- Lemma 3.4, p.12: an actual simple path, with every variable node in disagreement. -/
theorem disagreement_along_path (Γ : Language) (V : Type) [Fintype V]
    (I : Instance Γ V) (hI : MinimallyUnsatisfiable I)
    (c c' : Occurrence I) (hcc' : c ≠ c') (x y : V → Bool)
    (hx : Solution (I.delete (occurrenceConstraint I c)) x)
    (hy : Solution (I.delete (occurrenceConstraint I c')) y) :
    ∃ p : (incidenceGraph I).Walk (.inr c) (.inr c'),
      p.IsPath ∧ ∀ v : V, Sum.inl v ∈ p.support → x v ≠ y v := by sorry

end StabilityDichotomies.Solvability
