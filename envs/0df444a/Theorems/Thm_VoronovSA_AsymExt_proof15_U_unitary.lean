-- Prove2me | Theorems.Thm_VoronovSA_AsymExt_proof15_U_unitary
-- name    : VoronovSA.AsymExt.proof15_U_unitary
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:23:28.407567+00:00
-- url     : https://prove2.me/theorems/f1956776-2186-49bd-a2b5-e6e40af220c3
-- title:
--   Proof of Theorem 15 (p. 68) — U = Y X⁻¹ is unitary
-- statement:
--   In the setting of the previous step, let $\hat f$ be symmetric with orthonormal bases $\{e_{+,a}\}$ of $D_+=\ker(\hat f^+-i)$ and $\{e_{-,a}\}$ of $D_-=\ker(\hat f^++i)$, $m>0$. Let $w_1,\dots,w_m\in D_{f^+}$ be linearly independent modulo $D_{\bar f}$ with $\omega_*(w_k,w_l)=0$ for all $k,l$, decomposed as
--   $$w_k=\sum_{a}X_{ak}\,e_{+,a}+\sum_{a}Y_{ak}\,e_{-,a}+\underline\xi_k,\qquad\underline\xi_k\in D_{\bar f}.$$
--   Then the matrix
--   $$U=YX^{-1}$$
--   is unitary.
--
--   With $U$ unitary, $w_k=\sum_aX_{ak}e_{U,a}+\underline\xi_k$, so by (142) the family $\{w_k\}$ cuts out the self-adjoint extension $\hat f_U$ of Theorem 3. This is the converse of Theorem 15.
--
--   **Formalization Note** `X⁻¹` is Mathlib's matrix inverse (the zero matrix when $\det X=0$); the hypotheses force $\det X\ne0$ by the previous milestone. Unitarity is membership in `Matrix.unitaryGroup (Fin m) ℂ` ($U^*U=UU^*=1$). $z=i$ throughout.
--   **Formalization Note** $H$ is a complex Hilbert space (`InnerProductSpace ℂ H`, `CompleteSpace H`); operators are `LinearPMap`s $H\to H$, with Mathlib's adjoint `f.adjoint` and closure `f.closure`. Mathlib's inner product is conjugate-linear in the first argument, as in the paper. Symmetry is the published `TeschlQM.Shared.IsSymmetric` (densely defined and $(\eta,f\xi)=(f\eta,\xi)$ on $D_f$).
-- source:
--   Voronov, Gitman & Tyutin, Self-adjoint differential operators assosiated with self-adjoint differential expressions, arXiv:quant-ph/0603187v2, p. 68, proof of Theorem 15 (U = YX⁻¹ unitary)

import Mathlib
import Definitions.Def_TeschlQM_Shared_IsSymmetric
import Definitions.Def_TeschlQM_SelfAdjoint_addScalar
import Definitions.Def_VoronovSA_AsymExt_AsymForm

namespace VoronovSA.AsymExt

open scoped InnerProductSpace
open TeschlQM.SelfAdjoint

/-- Voronov–Gitman–Tyutin, proof of Theorem 15, Sec. 3.7, p. 68. In the setting of the
preceding step (`w_k = ∑_a X_{ak} e_{+,a} + ∑_a Y_{ak} e_{−,a} + ξ_k`, `ξ_k ∈ D_{f̄}`, the `w_k` linearly
independent modulo `D_{f̄}` with `ω*(w_k, w_l) = 0`), the matrix `U = Y X⁻¹` is unitary. -/
theorem proof15_U_unitary {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (f : H →ₗ.[ℂ] H) (hf : TeschlQM.Shared.IsSymmetric f) (m : ℕ) (hm : 0 < m)
    (eP : OrthonormalBasis (Fin m) ℂ (kerAdd f.adjoint (-Complex.I)))
    (eM : OrthonormalBasis (Fin m) ℂ (kerAdd f.adjoint Complex.I))
    (w : Fin m → f.adjoint.domain) (hw : LinIndepModClosure f w)
    (hiso : ∀ k l, asymForm f (w k) (w l) = 0)
    (X Y : Matrix (Fin m) (Fin m) ℂ) (ξ : Fin m → H) (hξ : ∀ k, ξ k ∈ f.closure.domain)
    (hdec : ∀ k, (w k : H) = ∑ a, X a k • (eP a : H) + ∑ a, Y a k • (eM a : H) + ξ k) :
    Y * X⁻¹ ∈ Matrix.unitaryGroup (Fin m) ℂ := by sorry

end VoronovSA.AsymExt
