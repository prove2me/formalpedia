-- Prove2me | Theorems.Thm_WassDDRO_Extremal_lemma_4_5
-- name    : WassDDRO.Extremal.lemma_4_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T06:56:09.070949+00:00
-- url     : https://prove2.me/theorems/17b29763-72d0-4d08-bf0e-148f9a384f79
-- title:
--   Lemma 4.5, pp. 14–15 — inf_z ⟨z, q − αξ̂⟩ + αf*(z) is the extended perspective of q ↦ −f(ξ̂ − q)
-- statement:
--   Let $E$ be a finite-dimensional real normed space and let $f : E \to \overline{\mathbb R}$ be proper (never $-\infty$, finite somewhere), convex and lower semicontinuous, with conjugate $f^*(z) = \sup_{\xi} \langle z, \xi\rangle - f(\xi)$. Fix a reference point $\hat\xi \in E$ and define, for $q \in E$ and $\alpha \ge 0$,
--   $$F(q,\alpha) = \inf_{z} \ \langle z, q - \alpha\hat\xi\rangle + \alpha f^*(z),$$
--   with $0 \cdot (+\infty) = 0$. Then $F$ is the extended perspective function of $q \mapsto -f(\hat\xi - q)$:
--   $$F(q,\alpha) = \begin{cases} -\alpha f(\hat\xi - q/\alpha) & \text{if } \alpha > 0,\\ -\chi_{\{0\}}(q) & \text{if } \alpha = 0,\end{cases}$$
--   where $-\chi_{\{0\}}(q)$ is $0$ for $q = 0$ and $-\infty$ otherwise.
--
--   The lemma is the step that turns the Lagrangian dual of program (12f) into the primal program (13) in the proof of Theorem 4.4.
--
--   **Formalization Note** $z$ ranges over the dual space `StrongDual ℝ E`. Convexity of $f$ is stated through its epigraph in $E \times \mathbb R$, since `ConvexOn` does not apply to `EReal`-valued functions. The product $\alpha f^*(z)$ at $\alpha = 0$ is Mathlib's `(0 : EReal) * ⊤ = 0`, which is the paper's convention. The two branches are stated as a conjunction of implications.
-- source:
--   Mohajerin Esfahani & Kuhn, arXiv:1505.05116v3, Lemma 4.5, pp. 14–15

import Mathlib
import Definitions.Def_WassDDRO_Extremal_Setting

namespace WassDDRO.Extremal

/-- Lemma 4.5, pp. 14–15. For a proper, convex, lower semicontinuous f : E → ℝ̄ and a reference
point ξ̂, the function F(q, α) = inf_z ⟨z, q − αξ̂⟩ + α f*(z) on E × ℝ₊ is the extended
perspective of q ↦ −f(ξ̂ − q): F(q, α) = −α f(ξ̂ − q/α) for α > 0, and F(q, 0) = −χ_{0}(q),
i.e. 0 if q = 0 and −∞ otherwise. The product α f*(z) at α = 0 is 0 (EReal: 0 · ⊤ = 0). -/
theorem lemma_4_5 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (f : E → EReal) (hf_ne_bot : ∀ ξ, f ξ ≠ ⊥) (hf_ne_top : ∃ ξ, f ξ ≠ ⊤)
    (hf_convex : Convex ℝ {p : E × ℝ | f p.1 ≤ (p.2 : EReal)})
    (hf_lsc : LowerSemicontinuous f)
    (ξh q : E) (α : ℝ) (hα : 0 ≤ α) :
    (0 < α →
      (⨅ z : StrongDual ℝ E, ((z (q - α • ξh) : ℝ) : EReal) + (α : EReal) * conjOn Set.univ f z)
        = -((α : EReal) * f (ξh - α⁻¹ • q))) ∧
    (α = 0 →
      (q = 0 →
        (⨅ z : StrongDual ℝ E, ((z (q - α • ξh) : ℝ) : EReal) + (α : EReal) * conjOn Set.univ f z)
          = 0) ∧
      (q ≠ 0 →
        (⨅ z : StrongDual ℝ E, ((z (q - α • ξh) : ℝ) : EReal) + (α : EReal) * conjOn Set.univ f z)
          = ⊥)) := by sorry

end WassDDRO.Extremal
