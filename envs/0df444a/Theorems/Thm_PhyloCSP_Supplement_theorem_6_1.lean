-- Prove2me | Theorems.Thm_PhyloCSP_Supplement_theorem_6_1
-- name    : PhyloCSP.Supplement.theorem_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T12:27:25.116908+00:00
-- url     : https://prove2.me/theorems/446d7d99-2648-47a7-8d98-21b066836c6a
-- title:
--   Theorem 6.1 — trivial approximation guarantee $\alpha_0=\max(a/12,\ a/21+b/7)$ for arity-4 predicates
-- statement:
--   Let $\varphi$ be a phylogenetic predicate of arity $4$, and let $a$ be the number of caterpillar patterns and $b$ the number of balanced (two-cherry) patterns in $\mathrm{Sat}(\varphi)$. Then the trivial approximation guarantee of $\varphi$ is
--   $$
--   \alpha_0(\varphi)=\max\Big(\frac{a}{12},\ \frac{a}{21}+\frac{b}{7}\Big).
--   $$
--   Here $\alpha_0(\varphi)$ is the infimum, over all instances of $\mathrm{CSP}(\varphi)$ with at least one constraint, of the largest fraction of constraints satisfied by a single tree. Thus the identity says both that every instance has a solution satisfying at least a $\max(a/12,\,a/21+b/7)$ fraction of its constraints and that no larger fraction can be guaranteed.
--
--   This is the baseline against which the nontrivial guarantees of Table 1 (Theorem 6.2) are measured.
--
--   **Formalization Note** $a$ and $b$ are the cardinalities of the caterpillar and non-caterpillar patterns in $\mathrm{Sat}(\varphi)$; on four leaves the non-caterpillar patterns are exactly the three balanced ones.
--
--   Differences from the source:
--   - reading: its trivial approximation guarantee α0 (named through the characterization of [CM23]) → trivialGuarantee φ: the infimum over instances of CSP(φ) with at least one constraint of the maximum over trees of the value; reason: pp.1–2 describe α0 as the guarantee obtainable on every instance; the paper proves both that bound and its optimality
--   - encoding: a satisfying caterpillar patterns and b satisfying balanced patterns → a = ncard of caterpillar patterns in Sat(φ), b = ncard of non-caterpillar patterns in Sat(φ); reason: on four leaves the non-caterpillars are the three balanced patterns (p.14)
--   - encoding: leaf labels 1, 2, 3, 4 → Fin 4; reason: Lean convention; same predicates
-- source:
--   Makarychev, Approximation Algorithms for Satisfiable Phylogenetic CSPs, STOC 2027 submission (manuscript sha256 3444b6c029bce73ce9a6ad0ae6bc8386c291dcb0b1e504e8216c60cd4d682dac), Theorem 6.1 and eq. (3), p.15 (PDF p.17); balanced patterns p.14 (PDF p.16); proof pp.16–17 (PDF pp.18–19)

import Mathlib
import Definitions.Def_PhyloCSP_Supplement_trivialGuarantee
import Definitions.Def_PhyloCSP_Supplement_Caterpillar

set_option autoImplicit false

namespace PhyloCSP

namespace Supplement

/-- Makarychev, *Approximation Algorithms for Satisfiable Phylogenetic CSPs*, STOC 2027 submission
(manuscript sha256 3444b6c0…682dac), Theorem 6.1 (Trivial approximation guarantee), p.15
(PDF p.17), eq. (3): "Let φ be a phylogenetic predicate of arity 4 with a satisfying caterpillar
patterns and b satisfying balanced patterns. Then its trivial approximation guarantee is
α0 = max(a/12, a/21 + b/7)." Balanced patterns (p.14, PDF p.16) are the three 4-leaf patterns that
are not caterpillars.

**Formalization Note.** `a` and `b` are the numbers of caterpillar and of non-caterpillar patterns
in `Sat(φ)`; `α₀` is `trivialGuarantee φ`, the infimum over instances of `CSP(φ)` with at least one
constraint of the optimal value. The equality asserts both halves of the proof: every instance has
a solution of value at least the right-hand side, and no larger constant works. -/
theorem theorem_6_1 (φ : Predicate 4) :
    trivialGuarantee φ =
      max ((({P | P ∈ φ ∧ IsCaterpillar P} : Set (Pattern (Fin 4))).ncard : ℝ) / 12)
        ((({P | P ∈ φ ∧ IsCaterpillar P} : Set (Pattern (Fin 4))).ncard : ℝ) / 21 +
          (({P | P ∈ φ ∧ ¬ IsCaterpillar P} : Set (Pattern (Fin 4))).ncard : ℝ) / 7) := by sorry

end Supplement

end PhyloCSP
