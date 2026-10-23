-- Prove2me | Theorems.Thm_VoronovSA_AsymExt_theorem_1
-- name    : VoronovSA.AsymExt.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:23:26.60477+00:00
-- url     : https://prove2.me/theorems/e25fd40e-ca66-4e90-a21b-9d7a717d95b9
-- title:
--   Theorem 1 (first von Neumann theorem) — D(f⁺) = D_f̄ ∔ ℵ_z̄ ∔ ℵ_z uniquely, and f⁺ξ* = f̄ξ + zξ_z + z̄ξ_z̄
-- statement:
--   Let $\hat f$ be a symmetric operator in a complex Hilbert space $\mathcal H$, with closure $\bar f$ and adjoint $\hat f^{+}$, and let $z\in\mathbb C$ with $\operatorname{Im}z\ne0$. Write $\aleph_{\bar z}=\ker(\hat f^{+}-z)$ and $\aleph_z=\ker(\hat f^{+}-\bar z)$ for the deficient subspaces. Then:
--
--   1. the domain of the adjoint is spanned by the three subspaces (eq. (4)),
--   $$D_{f^+}=D_{\bar f}+\aleph_{\bar z}+\aleph_{z};$$
--   2. every $\xi_*\in D_{f^+}$ has a **unique** representation (eq. (5))
--   $$\xi_*=\underline{\xi}+\xi_z+\xi_{\bar z},\qquad \underline\xi\in D_{\bar f},\ \xi_z\in\aleph_{\bar z},\ \xi_{\bar z}\in\aleph_z;$$
--   3. for any such representation the adjoint acts by (eq. (6))
--   $$\hat f^{+}\xi_*=\bar f\underline{\xi}+z\,\xi_z+\bar z\,\xi_{\bar z}.$$
--
--   This is the structural description of the adjoint's domain on which every later computation of the paper rests: the asymmetry form of the adjoint is evaluated through it in (18)–(19), and the proof of Theorem 15 decomposes the vectors $w_k$ by it.
--
--   **Formalization Note** $\aleph_{\bar z}$ is `kerAdd f.adjoint (-z)` and $\aleph_z$ is `kerAdd f.adjoint (-(conj z))` (footnote 12 of the paper: $\aleph_{\bar z}$ holds the eigenvectors for $z$). Clause 1 is an equality of submodules of $H$ (`⊔` is the sum of subspaces). Clause 2 is `∃!` over triples in $D_{\bar f}\times\aleph_{\bar z}\times\aleph_z$. Clause 3 uses `f.closure` on the $D_{\bar f}$-component.
--   **Formalization Note** $H$ is a complex Hilbert space (`InnerProductSpace ℂ H`, `CompleteSpace H`); operators are `LinearPMap`s $H\to H$, with Mathlib's adjoint `f.adjoint` and closure `f.closure`. Mathlib's inner product is conjugate-linear in the first argument, as in the paper. Symmetry is the published `TeschlQM.Shared.IsSymmetric` (densely defined and $(\eta,f\xi)=(f\eta,\xi)$ on $D_f$).
-- source:
--   Voronov, Gitman & Tyutin, Self-adjoint differential operators assosiated with self-adjoint differential expressions, arXiv:quant-ph/0603187v2, p. 8, Theorem 1, eqs. (4)–(6)

import Mathlib
import Definitions.Def_TeschlQM_Shared_IsSymmetric
import Definitions.Def_TeschlQM_SelfAdjoint_addScalar
import Definitions.Def_VoronovSA_AsymExt_AsymForm

namespace VoronovSA.AsymExt

open scoped InnerProductSpace
open TeschlQM.SelfAdjoint

/-- Voronov–Gitman–Tyutin, Theorem 1 (first von Neumann theorem), p. 8. For a symmetric `f` and
`z ∉ ℝ`, `D_{f⁺} = D_{f̄} ∔ ℵ_z̄ ∔ ℵ_z` with `ℵ_z̄ = Ker(f⁺ − z)` and `ℵ_z = Ker(f⁺ − z̄)`: the three
subspaces span `D_{f⁺}` (4), every `ξ* ∈ D_{f⁺}` decomposes uniquely as `ξ* = ξ + ξ_z + ξ_z̄` (5), and
then `f⁺ξ* = f̄ξ + z ξ_z + z̄ ξ_z̄` (6). -/
theorem theorem_1 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (f : H →ₗ.[ℂ] H) (hf : TeschlQM.Shared.IsSymmetric f) (z : ℂ) (hz : z.im ≠ 0) :
    f.closure.domain ⊔ kerAdd f.adjoint (-z) ⊔ kerAdd f.adjoint (-(starRingEnd ℂ z)) =
        f.adjoint.domain ∧
      (∀ x : f.adjoint.domain, ∃! p : f.closure.domain × kerAdd f.adjoint (-z) ×
          kerAdd f.adjoint (-(starRingEnd ℂ z)),
          (x : H) = (p.1 : H) + (p.2.1 : H) + (p.2.2 : H)) ∧
      (∀ (x : f.adjoint.domain) (ξ : f.closure.domain) (ξz : kerAdd f.adjoint (-z))
          (ξzb : kerAdd f.adjoint (-(starRingEnd ℂ z))),
          (x : H) = (ξ : H) + (ξz : H) + (ξzb : H) →
          f.adjoint x = f.closure ξ + z • (ξz : H) + (starRingEnd ℂ z) • (ξzb : H)) := by sorry

end VoronovSA.AsymExt
