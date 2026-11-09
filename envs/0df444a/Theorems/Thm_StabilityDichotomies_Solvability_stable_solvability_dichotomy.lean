-- Prove2me | Theorems.Thm_StabilityDichotomies_Solvability_stable_solvability_dichotomy
-- name    : StabilityDichotomies.Solvability.stable_solvability_dichotomy
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:06:00.582514+00:00
-- url     : https://prove2.me/theorems/7136f7c5-d7f5-4aa3-963d-10379e887b97
-- title:
--   Theorem 3.1 — finite duality characterizes stable solvability
-- statement:
--   Let $\Gamma$ be a finite nonempty language of nonempty Boolean relations of positive arity. Set $r_\Gamma=\max_{R\in\Gamma}r(R)$ and $\kappa_\Gamma=\sum_{R\in\Gamma}2^{r(R)}|R|^2>0$. Exactly one of the following holds:
--
--   1. $\Gamma$ has finite duality, and there is one deterministic exact solver $D_\Gamma$ with
--      $$\forall\text{ satisfiable }I,\qquad\operatorname{ASens}(D_\Gamma,I)\le r_\Gamma.$$
--   2. $\Gamma$ lacks finite duality, and every randomized exact solver $A$ satisfies
--      $$\forall n\ge8\ \exists\text{ satisfiable }I\text{ on }n\text{ variables},\qquad
--      \operatorname{ASens}(A,I)\ge\frac{n}{96\kappa_\Gamma}.$$
--
--   The constants and the size set $\{n:n\ge8\}$ are fixed by the language before the solver is chosen. Instances may depend on $A$ and $n$. Solver laws range over all finite inputs and arbitrary real probabilities, without any computational bound. Correctness is required only on satisfiable inputs. Deletion preserves all variables and removes one multiset occurrence; sensitivity uses unnormalized Hamming cost and all couplings.
--
--   This is the complete two-branch classification, with the source proof's quantitative witnesses: $r_\Gamma$ on p.11, $\kappa_\Gamma$ on p.14, and the all-$n\ge8$ lower estimate on p.15. These instantiate the printed $O_\Gamma(1)$ and $\Omega_\Gamma(n)$ statements and its existential unbounded size set. Finite duality is the semantic Definition 2.4, never a stable-solver assumption.
--
--   Differences from the source:
--   - generalization: OΓ(1) and ΩΓ(n) on a language-dependent unbounded set of sizes → upper bound rΓ and lower bound n/(96κΓ) for every n≥8, retaining both exclusive branches; reason: the source proves these exact uniform bounds on pp.11,14–15; the explicit size set is unbounded
--   - encoding: finite Boolean variable sets and multiset constraints → arbitrary finite types, Bool, Fin arity coordinates, and Multiset constraints; reason: bijections preserve all assignments and constraints, while retaining repeated scopes and occurrence multiplicities
--   - encoding: randomized algorithms and minimum expected Hamming distance over all couplings → one total PMF law family on every finite carrier, deterministic point masses, and a real infimum over the referenced real coupling matrices; reason: the classification is information-theoretic; finite normalized laws give a nonempty compact coupling polytope and attained bounded cost
--   - encoding: exactly one branch and an n-variable hard instance → Xor of the full branches and a hard instance on Fin n; reason: Xor is exclusive disjunction; relabel the constructed core and padding once before querying the unrestricted solver, with no permutation-invariance assumption
--   - generalization: the introduction uses n≥2 for the sensitivity classification → the deterministic upper bound and solver correctness also cover carriers of size zero or one; reason: Hamming transport on these carriers is at most one, while rΓ≥1; any solver on n≥2 inputs extends correctly to smaller inputs without changing its larger-input laws, so the lower branch excludes no source solver
-- source:
--   Chunyang Wang, Yuichi Yoshida, Stability Dichotomies for Boolean Constraint Satisfaction Problems, STOC 2027 submission #535 (October 2026), p.11, Theorem 3.1; quantitative proof pp.11,14–15; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf

import Definitions.Def_StabilityDichotomies_Solvability_FiniteDuality
import Definitions.Def_StabilityDichotomies_Solvability_Stability

namespace StabilityDichotomies.Solvability

/-- Theorem 3.1, p.11, with the proof-supported explicit constants (pp.11,14–15).
The lower branch covers every n≥8 and every total randomized exact solver, with
no running-time, symmetry, bounded-degree, or equivariance assumption. -/
theorem stable_solvability_dichotomy (Γ : Language) :
    Xor
      (FiniteDuality Γ ∧
        ∃ D : DeterministicSolver Γ,
          Solves (deterministicLaw D) ∧
          ∀ (V : Type) [Fintype V] (I : Instance Γ V), Satisfiable I →
            averageSensitivity (deterministicLaw D) I ≤ (maxArity Γ : ℝ))
      (¬ FiniteDuality Γ ∧
        ∀ A : Solver Γ, Solves A →
          ∀ n : ℕ, 8 ≤ n → ∃ I : Instance Γ (Fin n),
            Satisfiable I ∧
            (n : ℝ) / (96 * (kappa Γ : ℝ)) ≤ averageSensitivity A I) := by sorry

end StabilityDichotomies.Solvability
