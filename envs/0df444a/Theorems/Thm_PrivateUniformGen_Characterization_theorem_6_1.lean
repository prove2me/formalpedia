-- Prove2me | Theorems.Thm_PrivateUniformGen_Characterization_theorem_6_1
-- name    : PrivateUniformGen.Characterization.theorem_6_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:11:58.486401+00:00
-- url     : https://prove2.me/theorems/9728b219-6261-4dba-8178-c9fbdca8065b
-- title:
--   Theorem 6.1 — Closure, Helly and branching lower bounds
-- statement:
--   There is an absolute constant $a>0$ with the following property. For every language class $C$ on a countable space and every positive $n$, suppose $A$ is a private uniform generator with $0\le\varepsilon\le1$ and $0\le\delta\le1/(12n)$. Then all of the following hold:
--
--   $$\operatorname{CDim}(C)+1\le n,\qquad h_{\mathrm{fin}}(C)\le n,\qquad \operatorname{NBDim}(C)<\infty,\qquad a\log^*\operatorname{NBDim}(C)\le n.$$
--
--   The first two inequalities are in extended ordered types and therefore also force finiteness. No finite-dimension hypothesis is imposed. This is the lower-bound milestone for the characterization.
--
--   Differences from the source:
--   - reading: measurable subsets of the output range → the product sigma-algebra on subsets of X; randomized algorithms are arbitrary maps to probability laws; reason: membership events generate this sigma-algebra; X is countable, all stated utility events are measurable, and the upper-bound laws have finite support; no computability requirement is imposed by the source
--   - encoding: randomized algorithms and probability-one guarantees → ProbabilityMeasure-valued maps and almost-everywhere predicates; reason: bundles probability one for every input and expresses the identical almost-sure events without allowing zero measures
--   - encoding: CDim in {-1,0,1,...,infinity} and nonnegative ranks with infinity → WithTop integers for CDim and extended naturals for ranks and Helly numbers; reason: retains both -1 and infinity; finite-value projections are used only where finiteness is assumed or follows from the source results
--   - encoding: absolute constants in O and Omega → a positive real constant existentially quantified before all types, classes, privacy parameters, sample sizes and mechanisms; reason: makes the uniformity of the asymptotic notation explicit, with integer thresholds rounded upward by their comparison to the real bound
--   - reading: Omega(log* NBDim(C)), including potentially infinite dimension → explicit finiteness of NBDim(C) together with the numerical bound on its finite value; reason: the proof on p. 26 rules out binary trees of unbounded depth and then derives finiteness of the unrestricted dimension
--   - generalization: Theorem 6.1 requires 0 < delta → allows delta = 0 as well; reason: the proof uses only delta ≤ 1/(12n), as in the introduction Theorem 1.3; alternatively a pure mechanism is private for every positive smaller error
-- source:
--   Di Wang, Peng Ye, STOC 2027 submission #178 (October 2026), Theorem 6.1, p. 21. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/178.pdf

import Mathlib
import Definitions.Def_PrivateUniformGen_Characterization_Bounds

open MeasureTheory

namespace PrivateUniformGen.Characterization

theorem theorem_6_1  :
  ∃ c : ℝ, 0 < c ∧ ∀ (X : Type) [Countable X] (C : LanguageClass X)
    (n : ℕ), 1 ≤ n → ∀ (A : Mechanism X (Set X) n) (ε δ : ℝ),
    0 ≤ ε → ε ≤ 1 → 0 ≤ δ → δ ≤ 1 / (12 * (n : ℝ)) →
    IsDP A ε δ → IsUniformGenerator C A →
    closureDim C + 1 ≤ (n : WithTop ℤ) ∧ hellyNumber C.languages ≤ (n : ℕ∞) ∧
      nbDim C ⊤ < ⊤ ∧ c * (logStar (nbDim C ⊤).toNat : ℝ) ≤ (n : ℝ) := by sorry

end PrivateUniformGen.Characterization
