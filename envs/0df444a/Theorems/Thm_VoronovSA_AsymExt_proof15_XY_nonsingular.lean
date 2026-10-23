-- Prove2me | Theorems.Thm_VoronovSA_AsymExt_proof15_XY_nonsingular
-- name    : VoronovSA.AsymExt.proof15_XY_nonsingular
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:23:30.709673+00:00
-- url     : https://prove2.me/theorems/1dbc9a16-e43e-43e5-860d-8948b502ba1f
-- title:
--   Proof of Theorem 15 (p. 67) — for admissible w_k = Σ X_{ak} e_{+,a} + Σ Y_{ak} e_{−,a} + ξ_k, both X and Y are nonsingular
-- statement:
--   Let $\hat f$ be a symmetric operator in a complex Hilbert space $\mathcal H$, with orthonormal bases $\{e_{+,a}\}_{a=1}^m$ of $D_+=\ker(\hat f^+-i)$ and $\{e_{-,a}\}_{a=1}^m$ of $D_-=\ker(\hat f^++i)$, $m>0$. Let $w_1,\dots,w_m\in D_{f^+}$ satisfy
--
--   1. linear independence modulo $D_{\bar f}$: $\sum_k c_kw_k\in D_{\bar f}\Rightarrow c=0$;
--   2. $\omega_*(w_k,w_l)=0$ for all $k,l$ (relation (143)).
--
--   Suppose the $w_k$ are written as in the first von Neumann theorem at $z=i$,
--   $$w_k=\sum_{a=1}^m X_{ak}\,e_{+,a}+\sum_{a=1}^m Y_{ak}\,e_{-,a}+\underline\xi_k,\qquad \underline\xi_k\in D_{\bar f}.$$
--   Then the coefficient matrices are nonsingular:
--   $$\det X\ne0\quad\text{and}\quad\det Y\ne0 .$$
--
--   This is the first step of the converse direction of Theorem 15: it allows the family $\{w_k\}$ to be rewritten in terms of the vectors $e_{U,k}$ of (37).
--
--   **Formalization Note** The decomposition is a hypothesis on the underlying vectors in $H$, with $\underline\xi_k$ given as vectors of $H$ in `f.closure.domain`; that such a decomposition exists is Theorem 1. $z=i$ throughout.
--   **Formalization Note** $H$ is a complex Hilbert space (`InnerProductSpace ℂ H`, `CompleteSpace H`); operators are `LinearPMap`s $H\to H$, with Mathlib's adjoint `f.adjoint` and closure `f.closure`. Mathlib's inner product is conjugate-linear in the first argument, as in the paper. Symmetry is the published `TeschlQM.Shared.IsSymmetric` (densely defined and $(\eta,f\xi)=(f\eta,\xi)$ on $D_f$).
-- source:
--   Voronov, Gitman & Tyutin, Self-adjoint differential operators assosiated with self-adjoint differential expressions, arXiv:quant-ph/0603187v2, p. 67, proof of Theorem 15 (conditions 1)–3), nonsingularity of X and Y)

import Mathlib
import Definitions.Def_TeschlQM_Shared_IsSymmetric
import Definitions.Def_TeschlQM_SelfAdjoint_addScalar
import Definitions.Def_VoronovSA_AsymExt_AsymForm

namespace VoronovSA.AsymExt

open scoped InnerProductSpace
open TeschlQM.SelfAdjoint

/-- Voronov–Gitman–Tyutin, proof of Theorem 15, Sec. 3.7, p. 67. Let `f` be symmetric with
orthonormal bases `e_{+,a}` of `D₊ = Ker(f⁺ − i)` and `e_{−,a}` of `D₋ = Ker(f⁺ + i)` (`m > 0` vectors
each), and let `w_1, …, w_m ∈ D_{f⁺}` be linearly independent modulo `D_{f̄}` with `ω*(w_k, w_l) = 0`.
If `w_k = ∑_a X_{ak} e_{+,a} + ∑_a Y_{ak} e_{−,a} + ξ_k` with `ξ_k ∈ D_{f̄}` (the decomposition of
Theorem 1 at `z = i`), then the matrices `X` and `Y` are nonsingular. -/
theorem proof15_XY_nonsingular {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (f : H →ₗ.[ℂ] H) (hf : TeschlQM.Shared.IsSymmetric f) (m : ℕ) (hm : 0 < m)
    (eP : OrthonormalBasis (Fin m) ℂ (kerAdd f.adjoint (-Complex.I)))
    (eM : OrthonormalBasis (Fin m) ℂ (kerAdd f.adjoint Complex.I))
    (w : Fin m → f.adjoint.domain) (hw : LinIndepModClosure f w)
    (hiso : ∀ k l, asymForm f (w k) (w l) = 0)
    (X Y : Matrix (Fin m) (Fin m) ℂ) (ξ : Fin m → H) (hξ : ∀ k, ξ k ∈ f.closure.domain)
    (hdec : ∀ k, (w k : H) = ∑ a, X a k • (eP a : H) + ∑ a, Y a k • (eM a : H) + ξ k) :
    X.det ≠ 0 ∧ Y.det ≠ 0 := by sorry

end VoronovSA.AsymExt
