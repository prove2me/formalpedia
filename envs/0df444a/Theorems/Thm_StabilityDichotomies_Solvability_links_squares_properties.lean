-- Prove2me | Theorems.Thm_StabilityDichotomies_Solvability_links_squares_properties
-- name    : StabilityDichotomies.Solvability.links_squares_properties
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:05:48.061872+00:00
-- url     : https://prove2.me/theorems/a2961b78-8349-4090-a9e8-2ff9c2aa4144
-- title:
--   Lemma 3.7 — both properties of the fixed links-and-squares instance
-- statement:
--   Let $\Gamma$ lack finite duality. For every integer $N\ge1$, let $I_N$ and $L_0,\ldots,L_N$ be exactly the instance and layers of Definition 3.6. Then both
--
--   $$\operatorname{Sol}(I_N)=\varnothing,\qquad
--   \forall k\in\{0,\ldots,N\},\quad\operatorname{Sol}(I_N[V_N\setminus L_k])\ne\varnothing.$$
--
--   The second clause deletes a whole variable layer and all incident constraints. These two properties provide the obstruction needed for the sparse large-diameter milestone.
--
--   Differences from the source:
--   - encoding: finite Boolean variable sets and multiset constraints → arbitrary finite types, Bool, Fin arity coordinates, and Multiset constraints; reason: bijections preserve all assignments and constraints, while retaining repeated scopes and occurrence multiplicities
--   - encoding: endpoint-identified variables x_{i,a,b} and k in {0,…,N} → canonical representatives of the endpoint identifications, k : Fin (N+1), and induced subtype carriers; reason: representatives impose exactly the two stated identifications for N≥1 and preserve every generated occurrence
-- source:
--   Chunyang Wang, Yuichi Yoshida, Stability Dichotomies for Boolean Constraint Satisfaction Problems, STOC 2027 submission #535 (October 2026), p.13, Lemma 3.7; Definition 3.6, p.12; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf

import Definitions.Def_StabilityDichotomies_Solvability_FiniteDuality
import Definitions.Def_StabilityDichotomies_Solvability_LinksSquares

namespace StabilityDichotomies.Solvability

/-- Lemma 3.7, p.13: both properties of the actual Definition 3.6 instance. -/
theorem links_squares_properties (Γ : Language) (hΓ : ¬ FiniteDuality Γ)
    (N : ℕ) (hN : 1 ≤ N) :
    ¬ Satisfiable (linksSquares Γ N) ∧
      ∀ k : Fin (N + 1), Satisfiable ((linksSquares Γ N).induce
        (Finset.univ \ linkLayer N k)) := by sorry

end StabilityDichotomies.Solvability
