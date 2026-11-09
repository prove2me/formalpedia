-- Prove2me | Theorems.Thm_StabilityDichotomies_Solvability_boolean_finite_duality_criterion
-- name    : StabilityDichotomies.Solvability.boolean_finite_duality_criterion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:05:39.114216+00:00
-- url     : https://prove2.me/theorems/f09eff3d-a74c-4408-9436-9d6f62c2c1fe
-- title:
--   Proposition 2.6 — Boolean finite-duality criterion
-- statement:
--   Let $\Gamma$ be a finite nonempty Boolean constraint language whose relations are nonempty and have positive arity. Then
--
--   $$\Gamma\text{ has finite duality}\quad\Longleftrightarrow\quad
--   \Gamma\text{ is 0-valid, 1-valid, strictly essentially positive, or strictly essentially negative}.$$
--
--   Each class is a property of every member of the language, and the disjunction is outside that universal quantifier. The strict classes use CNFs on the original arguments with unit and same-sign clauses only. This connects the independent semantic obstruction property to the four relational classes used by the upper bound.
--
--   Differences from the source:
--   - encoding: finite Boolean variable sets and multiset constraints → arbitrary finite types, Bool, Fin arity coordinates, and Multiset constraints; reason: bijections preserve all assignments and constraints, while retaining repeated scopes and occurrence multiplicities
--   - encoding: CNF definitions on relation arguments → finite lists of clauses and signed coordinate literals; reason: existence of such a list is exactly existence of the source CNF; no extra variables or equality atoms are introduced
-- source:
--   Chunyang Wang, Yuichi Yoshida, Stability Dichotomies for Boolean Constraint Satisfaction Problems, STOC 2027 submission #535 (October 2026), p.9, Proposition 2.6; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf

import Definitions.Def_StabilityDichotomies_Solvability_FiniteDuality

namespace StabilityDichotomies.Solvability

/-- Proposition 2.6, p.9, including both directions and language-wide classes. -/
theorem boolean_finite_duality_criterion (Γ : Language) :
    FiniteDuality Γ ↔
      Valid Γ false ∨ Valid Γ true ∨
      StrictEssentialLanguage Γ true ∨ StrictEssentialLanguage Γ false := by sorry

end StabilityDichotomies.Solvability
