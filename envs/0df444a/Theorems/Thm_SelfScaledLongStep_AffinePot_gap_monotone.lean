-- Prove2me | Theorems.Thm_SelfScaledLongStep_AffinePot_gap_monotone
-- name    : SelfScaledLongStep.AffinePot.gap_monotone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T13:23:16.620793+00:00
-- url     : https://prove2.me/theorems/98d642b2-8d17-472c-83f3-100cdc5afe1c
-- title:
--   §7.2, p. 31 — ⟨s̃(λ), x̂⟩ = ⟨−F′(x̂), p(c)⟩ + λ((‖F′(x̂)‖∗_x̂)² − ‖p(d)‖²_x̂) is increasing in λ
-- statement:
--   Let $K$ be a self-scaled cone in $E$ with $\nu$-self-scaled barrier $F$, and consider the conic problem $(P)$: $\min \langle c, x\rangle$ subject to $Ax = b$, $x \in K$, with $A$ surjective and the dual $(D)$ strictly feasible. Let $\hat x \in S^0(P)$, i.e. $\hat x \in \operatorname{int} K$ and $A\hat x = b$. Let $p(c)$ and $p(d)$ be the projections of $c$ and of $d = F'(\hat x)$ into $\ker A$ with respect to $F''(\hat x)$, i.e.
--   $$Ap(u) = 0,\qquad A^*y(u) + F''(\hat x)p(u) = u\qquad (u = c,\ d),$$
--   and for $\lambda \in \mathbb R$ let $\tilde s(\lambda) = F''(\hat x)(p(c) + \lambda p(d)) - \lambda F'(\hat x)$. Then for every $\lambda$,
--   $$\langle \tilde s(\lambda), \hat x\rangle = \langle -F'(\hat x), p(c)\rangle + \lambda\Big(\big(\|F'(\hat x)\|^*_{\hat x}\big)^2 - \langle F'(\hat x), p(d)\rangle\Big) = \langle -F'(\hat x), p(c)\rangle + \lambda\Big(\big(\|F'(\hat x)\|^*_{\hat x}\big)^2 - \|p(d)\|^2_{\hat x}\Big),$$
--   and this gap is a nondecreasing function of $\lambda$. Here $\|u\|^*_{\hat x} = \langle u, [F''(\hat x)]^{-1}u\rangle^{1/2}$ and $\|p\|_{\hat x} = \langle F''(\hat x)p, p\rangle^{1/2}$.
--
--   The monotonicity is what makes the lower-bound update (7.17) well defined: the best dual bound obtainable from $\tilde s(\lambda) \in K^*$ is attained at the smallest admissible $\lambda$.
--
--   **Formalization Note** $E = E^* = \mathbb R^n$ through the inner product. $\|u\|^*_{\hat x}$ is `dnorm F x̂ u` and $\|p\|_{\hat x}$ is `lnorm F x̂ p` (the published 1998 setting drops the star). Nondegeneracy of $F''$ is part of the inherited barrier definition, and the conjugate barrier of the setting is an `sSup` over $\operatorname{int}K$; neither is used in this statement. The paper says "increasing"; the slope $(\|F'(\hat x)\|^*_{\hat x})^2 - \|p(d)\|^2_{\hat x} = \nu - \|p(d)\|^2_{\hat x}$ can be zero, so the statement is `Monotone` (nondecreasing), which is the true reading. The standing hypothesis $\nu \ge 1$ is carried as a binder (the paper derives it from pointedness). The §7 assumption that the objective is not constant on the feasible region is not needed here and is omitted.
-- source:
--   Nesterov & Todd, Self-scaled barriers and interior-point methods for convex programming, Math. Oper. Res. 22(1) (1997) 1–42, p. 31, §7.2, display before (7.17)

import Mathlib
import Definitions.Def_dualCone
import Definitions.Def_SelfScaledIPM_ShortStep_Setting
import Definitions.Def_SelfScaledIPM_ShortStep_Measures
import Definitions.Def_SelfScaledLongStep_AffinePot_Defs

open scoped InnerProductSpace
open SelfScaledIPM.ShortStep

namespace SelfScaledLongStep.AffinePot

/-- **§7.2, p. 31, display before (7.17).** With `pc = p(c)`, `pd = p(d)` the projections (7.12)
of `c` and `d = F'(x̂)`, the gap
`⟨s̃(λ), x̂⟩ = ⟨−F'(x̂), p(c)⟩ + λ((‖F'(x̂)‖*_x̂)² − ⟨F'(x̂), p(d)⟩)
           = ⟨−F'(x̂), p(c)⟩ + λ((‖F'(x̂)‖*_x̂)² − ‖p(d)‖²_x̂)`
is a (weakly) increasing function of `λ`. -/
theorem gap_monotone {n m : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsProperCone K)
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (ν : ℝ) (hν : 1 ≤ ν) (hF : IsSelfScaledBarrier K F ν)
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)) (hA : Function.Surjective A)
    (b : EuclideanSpace ℝ (Fin m)) (c : EuclideanSpace ℝ (Fin n))
    (hD : ∃ y s, IsDualStrict K A c y s)
    (xh : EuclideanSpace ℝ (Fin n)) (hxh : IsPrimalStrict K A b xh)
    (yc : EuclideanSpace ℝ (Fin m)) (pc : EuclideanSpace ℝ (Fin n))
    (hpc : SelfScaledLongStep.PrimalDual.IsProjection F A xh c yc pc)
    (yd : EuclideanSpace ℝ (Fin m)) (pd : EuclideanSpace ℝ (Fin n))
    (hpd : SelfScaledLongStep.PrimalDual.IsProjection F A xh (gradient F xh) yd pd) :
    (∀ t : ℝ, ⟪sTilde F xh pc pd t, xh⟫_ℝ =
        ⟪-gradient F xh, pc⟫_ℝ + t * ((dnorm F xh (gradient F xh)) ^ 2 - ⟪gradient F xh, pd⟫_ℝ)) ∧
    (∀ t : ℝ, ⟪sTilde F xh pc pd t, xh⟫_ℝ =
        ⟪-gradient F xh, pc⟫_ℝ + t * ((dnorm F xh (gradient F xh)) ^ 2 - (lnorm F xh pd) ^ 2)) ∧
    Monotone (fun t : ℝ => ⟪sTilde F xh pc pd t, xh⟫_ℝ) := by sorry

end SelfScaledLongStep.AffinePot
