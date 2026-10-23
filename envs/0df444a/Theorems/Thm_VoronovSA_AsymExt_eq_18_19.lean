-- Prove2me | Theorems.Thm_VoronovSA_AsymExt_eq_18_19
-- name    : VoronovSA.AsymExt.eq_18_19
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:23:19.851701+00:00
-- url     : https://prove2.me/theorems/09038f02-6ac3-4182-bddd-e6dcfd65623c
-- title:
--   (18)–(19) — ω*(η*, ξ*) = (z − z̄)[(η_z, ξ_z) − (η_z̄, ξ_z̄)] and Δ*(ξ*) = (z − z̄)(‖ξ_z‖² − ‖ξ_z̄‖²)
-- statement:
--   Let $\hat f$ be a symmetric operator in a complex Hilbert space $\mathcal H$, $z\in\mathbb C$ with $\operatorname{Im}z\ne0$, and $\omega_*$ the asymmetry form of the adjoint. Take $\eta_*,\xi_*\in D_{f^+}$ with decompositions as in the first von Neumann theorem,
--   $$\eta_*=\underline\eta+\eta_z+\eta_{\bar z},\qquad \xi_*=\underline\xi+\xi_z+\xi_{\bar z},$$
--   where $\underline\eta,\underline\xi\in D_{\bar f}$, $\eta_z,\xi_z\in\aleph_{\bar z}=\ker(\hat f^+-z)$ and $\eta_{\bar z},\xi_{\bar z}\in\aleph_z=\ker(\hat f^+-\bar z)$. Then, with $2iy=z-\bar z$,
--   $$\omega_*(\eta_*,\xi_*)=(z-\bar z)\big[(\eta_z,\xi_z)-(\eta_{\bar z},\xi_{\bar z})\big]\qquad(18)$$
--   and, for the quadratic form $\Delta_*(\xi_*)=\omega_*(\xi_*,\xi_*)$,
--   $$\Delta_*(\xi_*)=(z-\bar z)\big(\|\xi_z\|^2-\|\xi_{\bar z}\|^2\big).\qquad(19)$$
--
--   So the asymmetry of the adjoint comes entirely from the deficient components, and the two deficient subspaces contribute with opposite signs. Formula (19) is the von Neumann formula. The proof of Theorem 15 applies both identities at $z=i$.
--
--   **Formalization Note** The decompositions are hypotheses equating the underlying vectors in $H$, so the statement needs no separate proof that $D_{\bar f}\subseteq D_{f^+}$. $\aleph_{\bar z}$ is `kerAdd f.adjoint (-z)` and $\aleph_z$ is `kerAdd f.adjoint (-(conj z))`. The squared norms are real numbers cast to $\mathbb C$.
--   **Formalization Note** $H$ is a complex Hilbert space (`InnerProductSpace ℂ H`, `CompleteSpace H`); operators are `LinearPMap`s $H\to H$, with Mathlib's adjoint `f.adjoint` and closure `f.closure`. Mathlib's inner product is conjugate-linear in the first argument, as in the paper. Symmetry is the published `TeschlQM.Shared.IsSymmetric` (densely defined and $(\eta,f\xi)=(f\eta,\xi)$ on $D_f$).
-- source:
--   Voronov, Gitman & Tyutin, Self-adjoint differential operators assosiated with self-adjoint differential expressions, arXiv:quant-ph/0603187v2, p. 12, eqs. (18)–(19)

import Mathlib
import Definitions.Def_TeschlQM_Shared_IsSymmetric
import Definitions.Def_TeschlQM_SelfAdjoint_addScalar
import Definitions.Def_VoronovSA_AsymExt_AsymForm

namespace VoronovSA.AsymExt

open scoped InnerProductSpace
open TeschlQM.SelfAdjoint

/-- Voronov–Gitman–Tyutin (18)–(19), Sec. 2.6, p. 12 (von Neumann formula for the asymmetry forms).
For a symmetric `f`, `z ∉ ℝ`, and `η*, ξ* ∈ D_{f⁺}` decomposed as in Theorem 1,
`η* = η + η_z + η_z̄`, `ξ* = ξ + ξ_z + ξ_z̄` with `η, ξ ∈ D_{f̄}`, `η_z, ξ_z ∈ Ker(f⁺ − z)`,
`η_z̄, ξ_z̄ ∈ Ker(f⁺ − z̄)`:
`ω*(η*, ξ*) = (z − z̄)[(η_z, ξ_z) − (η_z̄, ξ_z̄)]` (18) and
`Δ*(ξ*) = ω*(ξ*, ξ*) = (z − z̄)(‖ξ_z‖² − ‖ξ_z̄‖²)` (19). -/
theorem eq_18_19 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (f : H →ₗ.[ℂ] H) (hf : TeschlQM.Shared.IsSymmetric f) (z : ℂ) (hz : z.im ≠ 0)
    (η ξ : f.adjoint.domain) (η₀ ξ₀ : f.closure.domain) (ηz ξz : kerAdd f.adjoint (-z))
    (ηzb ξzb : kerAdd f.adjoint (-(starRingEnd ℂ z)))
    (hη : (η : H) = (η₀ : H) + (ηz : H) + (ηzb : H))
    (hξ : (ξ : H) = (ξ₀ : H) + (ξz : H) + (ξzb : H)) :
    asymForm f η ξ = (z - starRingEnd ℂ z) * (⟪(ηz : H), (ξz : H)⟫_ℂ - ⟪(ηzb : H), (ξzb : H)⟫_ℂ) ∧
      asymForm f ξ ξ =
        (z - starRingEnd ℂ z) * (((‖(ξz : H)‖ ^ 2 - ‖(ξzb : H)‖ ^ 2 : ℝ)) : ℂ) := by sorry

end VoronovSA.AsymExt
