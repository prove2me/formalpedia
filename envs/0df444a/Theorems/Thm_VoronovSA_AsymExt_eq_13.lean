-- Prove2me | Theorems.Thm_VoronovSA_AsymExt_eq_13
-- name    : VoronovSA.AsymExt.eq_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:23:18.874898+00:00
-- url     : https://prove2.me/theorems/81367244-ca08-4253-b8b4-6518fce79da7
-- title:
--   (13) — the closure f̄ is the adjoint restricted to {ψ ∈ D(f⁺) : ω*(ξ*, ψ) = 0 for all ξ* ∈ D(f⁺)}
-- statement:
--   Let $\hat f$ be a symmetric operator in a complex Hilbert space $\mathcal H$, with closure $\bar f$, adjoint $\hat f^{+}$, and asymmetry form $\omega_*(\eta_*,\xi_*)=(\eta_*,\hat f^{+}\xi_*)-(\hat f^{+}\eta_*,\xi_*)$ on $D_{f^+}$. Then the closure is the restriction of the adjoint to the vectors that are $\omega_*$-orthogonal to the whole of $D_{f^+}$:
--   $$D_{\bar f}=\{\psi\in D_{f^+}:\ \omega_*(\xi_*,\psi)=0\ \ \forall\,\xi_*\in D_{f^+}\},\qquad \bar f\psi=\hat f^{+}\psi .$$
--
--   The identity describes the closure through the adjoint alone. The proof of Theorem 15 uses it to show that adding vectors of $D_{\bar f}$ to the $w_k$ changes neither the cut-out domain nor the relations $\omega_*(w_k,w_l)=0$.
--
--   **Formalization Note** The first clause is an equality of subsets of $H$: a vector lies in $D_{\bar f}$ exactly when it lies in $D_{f^+}$ and the form vanishes against every element of $D_{f^+}$. The rule $\bar f\psi=\hat f^+\psi$ is `f.closure ≤ f.adjoint` (domain inclusion and agreement).
--   **Formalization Note** $H$ is a complex Hilbert space (`InnerProductSpace ℂ H`, `CompleteSpace H`); operators are `LinearPMap`s $H\to H$, with Mathlib's adjoint `f.adjoint` and closure `f.closure`. Mathlib's inner product is conjugate-linear in the first argument, as in the paper. Symmetry is the published `TeschlQM.Shared.IsSymmetric` (densely defined and $(\eta,f\xi)=(f\eta,\xi)$ on $D_f$).
-- source:
--   Voronov, Gitman & Tyutin, Self-adjoint differential operators assosiated with self-adjoint differential expressions, arXiv:quant-ph/0603187v2, p. 11, eq. (13)

import Mathlib
import Definitions.Def_TeschlQM_Shared_IsSymmetric
import Definitions.Def_TeschlQM_SelfAdjoint_addScalar
import Definitions.Def_VoronovSA_AsymExt_AsymForm

namespace VoronovSA.AsymExt

open scoped InnerProductSpace
open TeschlQM.SelfAdjoint

/-- Voronov–Gitman–Tyutin (13), Sec. 2.5, p. 11: the closure `f̄` of a symmetric operator is the
restriction of the adjoint to the `ω*`-annihilator of `D_{f⁺}`:
`D_{f̄} = {ψ ∈ D_{f⁺} : ω*(ξ*, ψ) = 0 ∀ ξ* ∈ D_{f⁺}}` and `f̄ψ = f⁺ψ`. -/
theorem eq_13 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (f : H →ₗ.[ℂ] H) (hf : TeschlQM.Shared.IsSymmetric f) :
    (f.closure.domain : Set H) =
        {ψ | ∃ h : ψ ∈ f.adjoint.domain, ∀ ξ : f.adjoint.domain, asymForm f ξ ⟨ψ, h⟩ = 0} ∧
      f.closure ≤ f.adjoint := by sorry

end VoronovSA.AsymExt
