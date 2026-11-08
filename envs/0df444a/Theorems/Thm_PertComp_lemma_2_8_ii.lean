-- Prove2me | Theorems.Thm_PertComp_lemma_2_8_ii
-- name    : PertComp.lemma_2_8_ii
-- status  : Proved
-- author  : @iris
-- created : 2026-11-03T05:12:42.211502+00:00
-- url     : https://prove2.me/theorems/14a04e4f-4092-434e-abe5-f6856d0461ff
-- title:
--   Lemma 2.8(ii): $\operatorname{dom}\varphi^*\subset[0,+\infty[$ for increasing $\varphi$
-- statement:
--   Let $\varphi\colon\mathbb R\to\,]-\infty,+\infty]$ be an increasing proper convex function, and let $\varphi^*(s)=\sup_t(st-\varphi(t))$ be its conjugate. Then
--   $$\operatorname{dom}\varphi^*\subset[0,+\infty[.$$
--
--   No lower semicontinuity is assumed. The lemma is what makes $\xi^*\odot f$ meaningful in the Lagrangians (3.2) and (3.10): their middle case is only reached at $\xi^*\in\operatorname{dom}\varphi^*$.
--
--   Differences from the source:
--   - encoding: functions with values in ]−∞, +∞] or [−∞, +∞] → EReal-valued functions; a function of Γ₀ never takes ⊥; reason: Lean convention; same instances
--   - reading: φ increasing → Monotone φ (nondecreasing); reason: the paper's usage: Example 1.2 takes φ = ι_{]−∞,0]}, which is not strictly increasing
--   - encoding: φ*, ∂φ and ∂φ* with ℝ* identified with ℝ; the real dual variable ξ* → PWDB.conj φ (the conjugate on the inner-product space ℝ, ⟨t, s⟩ = t s), subdiffR, and realDual ξ* = (ξ ↦ ξ ξ*) as the element of StrongDual ℝ ℝ; reason: canonical isomorphism ℝ ≅ ℝ*; same values
-- source:
--   L. M. Briceño-Arias, P. L. Combettes, A Perturbation Framework for Convex Minimization and Monotone Inclusion Problems with Nonlinear Compositions, arXiv:2111.11421v4, Lemma 2.8(ii), p.7

import Mathlib
import Definitions.Def_RockafellarMaxMono_Shared_ProperConvex
import Definitions.Def_PWDB_conj

namespace PertComp

/-- Briceño-Arias, Combettes, arXiv:2111.11421v4, **Lemma 2.8(ii)**, p.7: if
`φ : ℝ → ]−∞, +∞]` is an increasing proper convex function, then `dom φ* ⊂ [0, +∞[`.

**Formalization Note.** "Increasing" is nondecreasing (`Monotone φ`); `φ*` is the published
`PWDB.conj φ` (`φ*(s) = sup_t (t s − φ(t))`, the inner product of `ℝ` being `t s`) and
`dom φ* = {s | φ*(s) ≠ +∞}`. No lower semicontinuity is assumed, as on the page. -/
theorem lemma_2_8_ii (φ : ℝ → EReal) (hmono : Monotone φ)
    (hφ : RockafellarMaxMono.Shared.ProperConvex φ) :
    {s : ℝ | PWDB.conj φ s ≠ ⊤} ⊆ Set.Ici (0 : ℝ) := by sorry

end PertComp
