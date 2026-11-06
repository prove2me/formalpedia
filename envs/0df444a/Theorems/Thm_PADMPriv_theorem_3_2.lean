-- Prove2me | Theorems.Thm_PADMPriv_theorem_3_2
-- name    : PADMPriv.theorem_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:09:19.890292+00:00
-- url     : https://prove2.me/theorems/72778674-2c21-4411-93ee-57e7bee8414f
-- title:
--   Theorem 3.2 — $T_F$ is $2/3$-averaged non-expansive
-- statement:
--   Let $F:\mathbb R^p\to\mathbb R$ and $g:\mathbb R^l\to\mathbb R$ be convex, $A$, $B$, $c$ as in model (1) and $\beta>0$. Then the PADM operator $T_F$ of (15) is $\tfrac23$-averaged non-expansive: there is a non-expansive $N:\mathbb R^m\to\mathbb R^m$ with
--   $$
--   T_F = \tfrac13 I + \tfrac23 N.
--   $$
--
--   Averagedness gives convergence of non-private PADM and, through non-expansiveness of every sample operator $T_{f_k}$, the privacy amplification results of Section 4.
--
--   **Formalization Note** $\alpha$-averaged is the published `ThreeOpSplitting.Convergence.IsAveraged` (Definition 5, including $\alpha\in(0,1)$). The proximal problems (13) are assumed to have minimizers at every input.
--
--   Differences from the source:
--   - encoding: the proximal operators P_{β,F,A}, P_{β,g,B} used as everywhere defined → hypotheses that (13) has a minimizer for F and for g at every input; reason: T_F is undefined otherwise; excludes only undefined cases
--   - generalization: full row rank of A and B (standing assumption, p.6) → not assumed; reason: the statement and its proof use only convexity and the proximal minimizers, never V or U; the source's case is an instance
-- source:
--   Li–Lai–Weng, Exact Feasibility and Privacy Amplification for Linearly Constrained Optimization, STOC 2027 submission (manuscript sha256 d58edbe0…0f3d), Theorem 3.2, p.8 (proof A.4, p.22)

import Mathlib
import Definitions.Def_PADMPriv_padmOp
import Definitions.Def_ThreeOpSplitting_Convergence_Nonexpansive

namespace PADMPriv

/-- Theorem 3.2 of Li–Lai–Weng, *Exact Feasibility and Privacy Amplification for Linearly Constrained Optimization*, STOC 2027 submission manuscript (sha256 d58edbe0…0f3d), p.8 (proof A.4, p.22): the operator `T_F` of (15) is
`2/3`-averaged non-expansive.

**Formalization Note** `F`, `g` real-valued convex, `β > 0` (p.7); `α`-averaged is the published
`ThreeOpSplitting.Convergence.IsAveraged` (Definition 5, p.8: `α ∈ (0, 1)` and
`T = (1 − α)I + αN` with `N` non-expansive). The proximal minimizers of (13) are assumed to
exist at every input, so that `T_F` is defined. -/
theorem theorem_3_2 {m p l : ℕ} (A : Matrix (Fin m) (Fin p) ℝ) (B : Matrix (Fin m) (Fin l) ℝ)
    (c : EuclideanSpace ℝ (Fin m)) (F : EuclideanSpace ℝ (Fin p) → ℝ)
    (g : EuclideanSpace ℝ (Fin l) → ℝ) (hF : ConvexOn ℝ Set.univ F)
    (hg : ConvexOn ℝ Set.univ g) (β : ℝ) (hβ : 0 < β)
    (hFprox : ∀ u, ∃ x, IsProxMin β F A u x) (hgprox : ∀ v, ∃ y, IsProxMin β g B v y) :
    ThreeOpSplitting.Convergence.IsAveraged (2 / 3) (padmOp β F g A B c) := by sorry

end PADMPriv
