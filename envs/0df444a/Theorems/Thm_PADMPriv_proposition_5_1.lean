-- Prove2me | Theorems.Thm_PADMPriv_proposition_5_1
-- name    : PADMPriv.proposition_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:09:12.337748+00:00
-- url     : https://prove2.me/theorems/acfc1f67-89cb-4e0c-b43b-201b1374f9c3
-- title:
--   Proposition 5.1 — contraction factors of $T_F$ under induced strong convexity
-- statement:
--   Let $F$, $g$ be convex and $\beta>0$. The operator $T_F$ of (15) is
--
--   1. $\tfrac12\big(\tfrac{\beta}{\beta+\varrho_F}+1\big)$-contractive if $F$ is $A$-induced $\varrho_F$-strongly convex;
--   2. $\tfrac12\big(1+\tfrac{\beta}{\beta+\varrho_g}\big)$-contractive if $g$ is $B$-induced $\varrho_g$-strongly convex;
--   3. $\tfrac12\big(\tfrac{\beta}{\beta+\varrho_F}+\tfrac{\beta}{\beta+\varrho_g}\big)$-contractive if both are.
--
--   Here $\tau$-contractive means $\|T_F(u)-T_F(v)\|_2\le\tau\|u-v\|_2$. All three factors are $<1$, so $T_F$ has a unique fixed point and the private iteration contracts towards it.
--
--   **Formalization Note** The three cases are three implications. The proximal problems (13) are assumed to have minimizers at every input.
--
--   Differences from the source:
--   - encoding: the proximal operators P_{β,F,A}, P_{β,g,B} used as everywhere defined → hypotheses that (13) has a minimizer for F and for g at every input; reason: T_F is undefined otherwise; excludes only undefined cases
--   - generalization: full row rank of A and B (standing assumption, p.6) → not assumed; reason: the statement and its proof use only convexity and the proximal minimizers, never V or U; the source's case is an instance
-- source:
--   Li–Lai–Weng, Exact Feasibility and Privacy Amplification for Linearly Constrained Optimization, STOC 2027 submission (manuscript sha256 d58edbe0…0f3d), Proposition 5.1, p.11 (proof A.13, pp.29–30)

import Mathlib
import Definitions.Def_PADMPriv_padmOp
import Definitions.Def_PADMPriv_IsContraction
import Definitions.Def_PADMPriv_IsInducedStronglyConvex

namespace PADMPriv

/-- Proposition 5.1 of Li–Lai–Weng, *Exact Feasibility and Privacy Amplification for Linearly Constrained Optimization*, STOC 2027 submission manuscript (sha256 d58edbe0…0f3d), p.11 (proof A.13, pp.29–30): the operator `T_F` is
`½(β/(β + ϱ_F) + 1)`-contractive if `F` is `A`-induced `ϱ_F`-strongly convex,
`½(1 + β/(β + ϱ_g))`-contractive if `g` is `B`-induced `ϱ_g`-strongly convex, and
`½(β/(β + ϱ_F) + β/(β + ϱ_g))`-contractive if both are.

**Formalization Note** The three cases are three implications. `F`, `g` real-valued convex, `β > 0`
(p.7); the proximal problems (13) are assumed to have minimizers, so that `T_F` is defined. -/
theorem proposition_5_1 {m p l : ℕ} (A : Matrix (Fin m) (Fin p) ℝ)
    (B : Matrix (Fin m) (Fin l) ℝ) (c : EuclideanSpace ℝ (Fin m))
    (F : EuclideanSpace ℝ (Fin p) → ℝ) (g : EuclideanSpace ℝ (Fin l) → ℝ)
    (hF : ConvexOn ℝ Set.univ F) (hg : ConvexOn ℝ Set.univ g) (β : ℝ) (hβ : 0 < β)
    (hFprox : ∀ u, ∃ x, IsProxMin β F A u x) (hgprox : ∀ v, ∃ y, IsProxMin β g B v y)
    (ϱF ϱg : ℝ) :
    (IsInducedStronglyConvex A ϱF F →
        IsContraction ((1 / 2) * (β / (β + ϱF) + 1)) (padmOp β F g A B c)) ∧
      (IsInducedStronglyConvex B ϱg g →
        IsContraction ((1 / 2) * (1 + β / (β + ϱg))) (padmOp β F g A B c)) ∧
      (IsInducedStronglyConvex A ϱF F → IsInducedStronglyConvex B ϱg g →
        IsContraction ((1 / 2) * (β / (β + ϱF) + β / (β + ϱg))) (padmOp β F g A B c)) := by sorry

end PADMPriv
