-- Prove2me | Theorems.Thm_StabilityDichotomies_Solvability_nonisolated_variables_bound
-- name    : StabilityDichotomies.Solvability.nonisolated_variables_bound
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T05:02:45.535205+00:00
-- url     : https://prove2.me/theorems/f6baf3e6-9042-45a7-9e49-37fa181561d3
-- title:
--   Non-isolated variables are bounded by arity times constraints
-- statement:
--   For a finite Boolean constraint language $\Gamma$ with maximum relation arity $r_\Gamma$ and any instance with $m$ constraint occurrences, at most $r_\Gamma m$ variables occur in a constraint. Repeated variables in a scope and repeated constraint occurrences are allowed. This is the combinatorial estimate used at the end of the sensitivity bound in the proof of Theorem 4.3.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean Constraint Satisfaction Problems, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf, proof of Theorem 4.3, p.17.

import Definitions.Def_StabilityDichotomies_Solvability_Model
noncomputable section
open scoped Classical BigOperators

namespace StabilityDichotomies.Solvability
theorem nonisolated_variables_bound {Γ : Language} {V : Type} [Fintype V]
    (I : Instance Γ V) :
    (I.constraints.toFinset.biUnion fun c => Finset.univ.image c.scope).card ≤
      maxArity Γ * I.constraints.card := by sorry
end StabilityDichotomies.Solvability
