-- Prove2me | Theorems.Thm_TeschlQM_Free_smooth_compact_core
-- name    : TeschlQM.Free.smooth_compact_core
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T01:06:47.581978+00:00
-- url     : https://prove2.me/theorems/60f463c5-e37d-49ff-96eb-18e42125aeb7
-- title:
--   Lemma 7.9 — C_c^∞(ℝⁿ) is a core for H₀
-- statement:
--   Let $C_c^\infty(\mathbb R^n) = \{f \in \mathcal S(\mathbb R^n) \mid \operatorname{supp}(f) \text{ is compact}\}$ be the smooth compactly supported functions, viewed as a subspace of $L^2(\mathbb R^n)$. Then $C_c^\infty(\mathbb R^n)$ is a **core** for the free Schrödinger operator $H_0$: $C_c^\infty(\mathbb R^n) \subseteq \mathfrak D(H_0)$ and
--   $$\overline{H_0|_{C_c^\infty(\mathbb R^n)}} = H_0 .$$
--
--   A core lets properties of $H_0$ (quadratic form, relative bounds of potentials) be checked on smooth compactly supported functions only.
--
--   **Formalization Note.** The subspace is the `Submodule.span` of the $L^2$ classes of smooth (`ContDiff ℝ ∞`) compactly supported functions; the set of such classes is already a subspace, so the span adds nothing. The closure is Mathlib's `LinearPMap.closure` of `domRestrict`.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 168, Lemma 7.9

import Mathlib
import Definitions.Def_TeschlQM_Free_freeHamiltonian

namespace TeschlQM.Free

open MeasureTheory
open scoped ContDiff

/-- Teschl, Lemma 7.9, p. 168: `C_c^∞(ℝⁿ) = {f ∈ 𝒮(ℝⁿ) | supp(f) is compact}` is a core for `H₀`:
it lies in `𝔇(H₀)` and the closure of the restriction `H₀|_{C_c^∞(ℝⁿ)}` is `H₀`. Here
`C_c^∞(ℝⁿ)` is the subspace of `L²(ℝⁿ)` spanned by the classes of smooth compactly supported
functions (the set of such classes is already a subspace). -/
theorem smooth_compact_core (n : ℕ) :
    let D : Submodule ℂ (Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :=
      Submodule.span ℂ
        {ψ | ∃ f : EuclideanSpace ℝ (Fin n) → ℂ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
          (ψ : EuclideanSpace ℝ (Fin n) → ℂ) =ᵐ[volume] f}
    D ≤ (freeHamiltonian n).domain ∧
      ((freeHamiltonian n).domRestrict D).closure = freeHamiltonian n := by sorry

end TeschlQM.Free
