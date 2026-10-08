-- Prove2me | Theorems.Thm_SelfScaledLongStep_PrimalDual_lemma_5_1
-- name    : SelfScaledLongStep.PrimalDual.lemma_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T12:22:43.583188+00:00
-- url     : https://prove2.me/theorems/73a85203-f27e-439e-8054-a321624f26c6
-- title:
--   Lemma 5.1, p. 19 — on D = {w + αv + βz : α, β ≥ 0}, ⟨F″(x)v, z⟩ = 0 and ⟨F‴(x)[z]v, v⟩ = ⟨F‴(x)[v]z, z⟩ = 0
-- statement:
--   Let $K$ be a self-scaled cone with a $\nu$-self-scaled barrier $F$. Fix $v\in\partial K$ with $v\ne0$, a point $w\in\operatorname{int}K$, and a direction $z\in\partial K$ **orthogonal to $v$ with respect to $w$**, that is $\langle F''(w)v,z\rangle=0$. Let
--   $$D=\{w+\alpha v+\beta z:\alpha\ge0,\ \beta\ge0\}.$$
--   Then for every $x\in D$,
--   $$\langle F''(x)v,z\rangle=0,\qquad(5.1)$$
--   $$\langle F'''(x)[z]v,v\rangle=0,\qquad\langle F'''(x)[v]z,z\rangle=0.\qquad(5.2)$$
--
--   The lemma is the first step towards the separability of a self-scaled barrier on the two-dimensional cone spanned by orthogonal boundary directions (Theorem 5.1).
--
--   **Formalization Note** The points of $D$ are written explicitly as $w+\alpha v+\beta z$ with $\alpha,\beta\ge0$. $F'''(x)[u]$ is `fderiv ℝ (hess F) x u`; every point of $D$ is interior to $K$, so the paper's right derivatives are ordinary derivatives. The barrier is nondegenerate as in the published setting; $\nu\ge1$ is a binder (derived in the paper, p. 3).
-- source:
--   Nesterov & Todd, Self-scaled barriers and interior-point methods for convex programming, Math. Oper. Res. 22(1) (1997) 1–42, p. 19, §5 preamble and Lemma 5.1, (5.1)–(5.2)

import Mathlib
import Definitions.Def_dualCone
import Definitions.Def_SelfScaledIPM_ShortStep_Setting
import Definitions.Def_SelfScaledIPM_ShortStep_Measures

open scoped InnerProductSpace
open SelfScaledIPM.ShortStep

namespace SelfScaledLongStep.PrimalDual

/-- **Lemma 5.1** (p. 19), with the standing hypotheses of §5: `v ∈ ∂K`, `v ≠ 0`, `w ∈ int K`,
and `z ∈ ∂K` orthogonal to `v` with respect to `w`, i.e. `⟨F''(w)v, z⟩ = 0`. For every
`x = w + αv + βz` with `α, β ≥ 0` (the set `D`):
(5.1) `⟨F''(x)v, z⟩ = 0`, and (5.2) `⟨F'''(x)[z]v, v⟩ = 0`, `⟨F'''(x)[v]z, z⟩ = 0`,
where `F'''(x)[u] = fderiv ℝ (hess F) x u`. -/
theorem lemma_5_1 {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsProperCone K)
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (ν : ℝ) (hν : 1 ≤ ν) (hF : IsSelfScaledBarrier K F ν)
    (v w z : EuclideanSpace ℝ (Fin n)) (hv : v ∈ frontier K) (hv0 : v ≠ 0)
    (hw : w ∈ interior K) (hz : z ∈ frontier K) (horth : ⟪hess F w v, z⟫_ℝ = 0)
    (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    ⟪hess F (w + α • v + β • z) v, z⟫_ℝ = 0 ∧
      ⟪fderiv ℝ (hess F) (w + α • v + β • z) z v, v⟫_ℝ = 0 ∧
      ⟪fderiv ℝ (hess F) (w + α • v + β • z) v z, z⟫_ℝ = 0 := by sorry

end SelfScaledLongStep.PrimalDual
