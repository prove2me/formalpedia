-- Prove2me | Theorems.Thm_PhyloCSP_equation_2
-- name    : PhyloCSP.equation_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:26:32.542843+00:00
-- url     : https://prove2.me/theorems/7d5a2e07-6fc3-486e-a7f1-32ef909bc51c
-- title:
--   Section 3.1, eq. (2) — the guarantee of a consistent transformation is a finite minimum
-- statement:
--   Let $F$ be a consistent tree transformation and $\varphi$ a predicate of arity $k$ with canonical relaxation $\varphi'$. Then
--   $$
--   p(\varphi,F)=\min_{P\in\mathrm{Sat}(\varphi')}\Pr\bigl(F[P]\in\mathrm{Sat}(\varphi)\bigr),
--   $$
--   where each pattern $P$ on the variables $x_1,\dots,x_k$ is evaluated as an input tree with these $k$ leaves.
--
--   So for consistent transformations it suffices to check the finitely many patterns satisfying $\varphi'$, instead of all trees of arbitrary size.
--
--   **Formalization Note** The patterns on the variables are carried to a leaf set $S\subseteq\mathbb N$ by any bijection; the minimum over the finite set is an infimum in $[0,\infty]$, equal to $\infty$ when $\mathrm{Sat}(\varphi')$ is empty.
--
--   Differences from the source:
--   - encoding: min over P ∈ Sat(φ′) of Pr(F[P] ∈ Sat(φ)), with P a tree on the variables → ⨅ over P ∈ Sat(φ′) in ℝ≥0∞, P carried to a leaf set S ⊆ ℕ by an arbitrary bijection e : Fin k ≃ S; reason: a minimum over a finite set is its infimum (⊤ when empty, as in eq. (1)); by relabeling equivariance every e gives the same value
--   - encoding: predicates as Boolean formulas in triplet atoms → their satisfying sets Sat(φ) on the variables Fin k; reason: p.1: every predicate is determined by Sat(φ) and every set of patterns is a predicate
-- source:
--   Makarychev, Approximation Algorithms for Satisfiable Phylogenetic CSPs, STOC 2027 submission (manuscript sha256 3444b6c029bce73ce9a6ad0ae6bc8386c291dcb0b1e504e8216c60cd4d682dac), Section 3.1, eq. (2), p.7 (PDF p.9)

import Mathlib
import Definitions.Def_PhyloCSP_Consistent
import Definitions.Def_PhyloCSP_pPred

set_option autoImplicit false

open scoped ENNReal

namespace PhyloCSP

/-- Makarychev, *Approximation Algorithms for Satisfiable Phylogenetic CSPs*, STOC 2027
submission (manuscript sha256 3444b6c0…682dac), Section 3.1, eq. (2), p.7 (PDF p.9): "For
consistent transformations, the formula for p(φ, F) is considerably simpler … The formula becomes
p(φ, F) = min_{P ∈ Sat(φ′)} Pr(F[P] ∈ Sat(φ)). (2)"

For a consistent `F` and a predicate `φ` of arity `k`, `p(φ, F)` is the minimum, over the patterns
`P` on the variables satisfying the canonical relaxation `φ′`, of the probability that the output
on `P` satisfies `φ`. The patterns on the variables `Fin k` are evaluated as trees on a leaf set
`S ⊆ ℕ` through any bijection `e : Fin k ≃ ↥S`.

**Formalization Note.** The minimum over the finite set `Sat(φ′)` is an infimum in `ℝ≥0∞`, `⊤`
when `Sat(φ′)` is empty. The statement holds for every labeling `e` (by equivariance they all
agree). -/
theorem equation_2 (F : TreeTransformation) (hF : Consistent F) {k : ℕ} (φ : Predicate k)
    (S : Finset ℕ) (e : Fin k ≃ ↥S) :
    pPred F φ = ⨅ P ∈ canonRelax φ,
      (F.law S (P.relabel e)).toOuterMeasure {Q | Q.relabel e.symm ∈ φ} := by sorry

end PhyloCSP
