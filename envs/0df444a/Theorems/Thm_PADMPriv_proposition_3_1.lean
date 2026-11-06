-- Prove2me | Theorems.Thm_PADMPriv_proposition_3_1
-- name    : PADMPriv.proposition_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:08:10.637469+00:00
-- url     : https://prove2.me/theorems/2d563555-d4e7-440b-adbb-deaf2e591fd3
-- title:
--   Proposition 3.1 — $A\circ P_{\beta,F,A}$ is single-valued and firmly non-expansive
-- statement:
--   Let $F:\mathbb R^p\to\mathbb R$ be convex, $A\in\mathbb R^{m\times p}$ and $\beta>0$. Then:
--
--   1. any two minimizers $x,x'$ of the proximal problem (13) at the same input $u$ satisfy $Ax = Ax'$, so $A\circ P_{\beta,F,A}$ is single-valued;
--   2. the operator $A\circ P_{\beta,F,A}$ is firmly non-expansive: for all $u,v\in\mathbb R^m$,
--   $$
--   \|A P_{\beta,F,A}(u) - A P_{\beta,F,A}(v)\|_2^2 \le \big\langle A P_{\beta,F,A}(u) - A P_{\beta,F,A}(v),\ u-v\big\rangle.
--   $$
--
--   This is the building block of the averagedness of $T_F$ (Theorem 3.2) and of the contraction bounds of Proposition 5.1.
--
--   **Formalization Note** Firm non-expansiveness is the published `ThreeOpSplitting.Convergence.IsFirmlyNonexpansive` (Definition 4). The minimizers of (13) are assumed to exist at every input.
--
--   Differences from the source:
--   - generalization: A ∘ P_{β,F,A} is firmly non-expansive → also concludes that any two minimizers of (13) at the same input have the same image under A; reason: this is the first step of the proof (p.22) and is needed for the operator to be well defined; the firm non-expansiveness clause is the source's claim
--   - encoding: P_{β,F,A} used as everywhere defined → hypothesis that (13) has a minimizer at every input; reason: the operator is undefined otherwise; excludes only undefined cases
--   - generalization: full row rank of A and B (standing assumption, p.6) → not assumed; reason: the statement and its proof use only convexity and the proximal minimizers, never V or U; the source's case is an instance
-- source:
--   Li–Lai–Weng, Exact Feasibility and Privacy Amplification for Linearly Constrained Optimization, STOC 2027 submission (manuscript sha256 d58edbe0…0f3d), Proposition 3.1, p.8 (proof A.3, pp.21–22)

import Mathlib
import Definitions.Def_PADMPriv_proxImage
import Definitions.Def_ThreeOpSplitting_Convergence_Nonexpansive

namespace PADMPriv

/-- Proposition 3.1 of Li–Lai–Weng, *Exact Feasibility and Privacy Amplification for Linearly Constrained Optimization*, STOC 2027 submission manuscript (sha256 d58edbe0…0f3d), p.8 (proof A.3, pp.21–22): the operator
`A ∘ P_{β,F,A}` is firmly non-expansive. The proof's first step is stated as the first clause: any
two minimizers of (13) at the same input have the same image under `A`, so `A ∘ P_{β,F,A}` is
single-valued.

**Formalization Note** `F` is real-valued and convex and `β > 0` (p.7). Firm non-expansiveness is
the published `ThreeOpSplitting.Convergence.IsFirmlyNonexpansive` (Definition 4, p.8). The
minimizers of (13) are assumed to exist at every input, so that `proxImage` is the operator
`A ∘ P_{β,F,A}` everywhere. -/
theorem proposition_3_1 {m p : ℕ} (A : Matrix (Fin m) (Fin p) ℝ)
    (F : EuclideanSpace ℝ (Fin p) → ℝ) (hF : ConvexOn ℝ Set.univ F) (β : ℝ) (hβ : 0 < β)
    (hFprox : ∀ u, ∃ x, IsProxMin β F A u x) :
    (∀ (u : EuclideanSpace ℝ (Fin m)) (x x' : EuclideanSpace ℝ (Fin p)),
        IsProxMin β F A u x → IsProxMin β F A u x' →
          Matrix.toEuclideanLin A x = Matrix.toEuclideanLin A x') ∧
      ThreeOpSplitting.Convergence.IsFirmlyNonexpansive (proxImage β F A) := by sorry

end PADMPriv
