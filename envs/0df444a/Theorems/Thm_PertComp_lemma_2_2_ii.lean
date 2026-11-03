-- Prove2me | Theorems.Thm_PertComp_lemma_2_2_ii
-- name    : PertComp.lemma_2_2_ii
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:14:20.278487+00:00
-- url     : https://prove2.me/theorems/5b85b2e3-efad-45d0-852b-d59800e64782
-- title:
--   Lemma 2.2(ii): conjugates of the perspective and of $\xi\odot f$
-- statement:
--   Let $X$ be a reflexive real Banach space, $f\in\Gamma_0(X)$ and $\xi\in[0,+\infty[$. Then
--   $$\big[\widetilde f(\cdot,\xi)\big]^*=\xi\odot f^*\qquad\text{and}\qquad(\xi\odot f)^*=\widetilde{f^*}(\cdot,\xi),$$
--   where $\widetilde f$ is the perspective (2.7), $\xi\odot\cdot$ is (2.8) (at $\xi=0$, the indicator of the closure of the domain), and $\widetilde{f^*}$ is the perspective of $f^*$. Both identities are equalities of functions on $X^*$, including at $\xi=0$.
--
--   The second identity converts $\sup_x(\langle x,-L^*y^*\rangle-(h+\xi^*\odot f)(x))$ into the infimal convolution of (3.11).
--
--   Differences from the source:
--   - encoding: functions with values in ]−∞, +∞] or [−∞, +∞] → EReal-valued functions; a function of Γ₀ never takes ⊥; reason: Lean convention; same instances
--   - encoding: reflexive real Banach space → NormedSpace ℝ with [CompleteSpace] and IsReflexive (the canonical map into the bidual is onto); reason: Mathlib has no reflexivity class; same spaces
--   - reading: closure (in (2.8)) and lower semicontinuity of functions on X* → for the norm topology of StrongDual ℝ X; reason: the sets and functions are convex and X is reflexive, so norm, weak and weak* closures (and lower semicontinuity) coincide
-- source:
--   L. M. Briceño-Arias, P. L. Combettes, A Perturbation Framework for Convex Minimization and Monotone Inclusion Problems with Nonlinear Compositions, arXiv:2111.11421v4, Lemma 2.2(ii), p.6

import Mathlib
import Definitions.Def_RockafellarMaxMono_Shared_Conj
import Definitions.Def_PertComp_IsReflexive
import Definitions.Def_TensorAHPE_IsProperClosedConvex
import Definitions.Def_PertComp_persp
import Definitions.Def_PertComp_odot

namespace PertComp

/-- Briceño-Arias, Combettes, arXiv:2111.11421v4, **Lemma 2.2(ii)**, p.6: let `X` be a reflexive
real Banach space, `f ∈ Γ₀(X)` and `ξ ∈ [0, +∞[`. Then `[f̃(·, ξ)]* = ξ ⊙ f*` and
`(ξ ⊙ f)* = \widetilde{f*}(·, ξ)`.

**Formalization Note.** Both identities are equalities of functions on `X*`. `f̃` is the
perspective (2.7) (`persp`), `ξ ⊙ ·` is (2.8) with the closure of the domain at `ξ = 0` (`odot`),
`\widetilde{f*}` is the perspective of `f* : X* → ]−∞, +∞]`. -/
theorem lemma_2_2_ii {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (hX : IsReflexive X) (f : X → EReal) (hf : TensorAHPE.IsProperClosedConvex f) (ξ : ℝ)
    (hξ : 0 ≤ ξ) :
    RockafellarMaxMono.Shared.conj (fun x => persp f x ξ) =
        odot ξ (RockafellarMaxMono.Shared.conj f) ∧
      RockafellarMaxMono.Shared.conj (odot ξ f) =
        fun x' => persp (RockafellarMaxMono.Shared.conj f) x' ξ := by sorry

end PertComp
