-- Prove2me | Theorems.Thm_VoronovSA_AsymExt_eq_142_143
-- name    : VoronovSA.AsymExt.eq_142_143
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:23:23.757991+00:00
-- url     : https://prove2.me/theorems/4233e8cd-ed7e-41fc-b4ff-6d14c6f52817
-- title:
--   (142)–(143) — w_k = Σ_a X_{ak} e_{U,a} + ξ_k (det X ≠ 0, ξ_k ∈ D_f̄) cut out the same extension and satisfy ω*(w_k, w_l) = 0
-- statement:
--   Keep the setting of (141): $\hat f$ symmetric, orthonormal bases $\{e_{+,k}\}$ of $D_+=\ker(\hat f^+-i)$ and $\{e_{-,l}\}$ of $D_-=\ker(\hat f^++i)$ of size $m>0$, $U$ unitary and $e_{U,k}=e_{+,k}+\sum_lU_{lk}e_{-,l}$. Let $X=(X_{ak})$ be an $m\times m$ matrix with $\det X\ne0$, let $\underline\xi_1,\dots,\underline\xi_m\in D_{\bar f}$, and put
--   $$w_k=\sum_{a=1}^m X_{ak}\,e_{U,a}+\underline\xi_k,\qquad k=1,\dots,m.$$
--   Then:
--
--   1. the $w_k$ cut out the same operator as the $e_{U,k}$:
--   $$\{\psi\in D_{f^+}:\ \omega_*(w_k,\psi)=0\ \forall k\}=\{\psi\in D_{f^+}:\ \omega_*(e_{U,k},\psi)=0\ \forall k\},\qquad(142)$$
--   and both operators act as $\hat f^+$;
--   2. $\omega_*(w_k,w_l)=0$ for all $k,l$ (143);
--   3. the $w_k$ are linearly independent modulo $D_{\bar f}$.
--
--   So the description of a self-adjoint extension by vectors of $D_{f^+}$ is invariant under nonsingular recombination and under shifts by vectors of $D_{\bar f}$. This completes the direction "every self-adjoint extension has the form (144)".
--
--   **Formalization Note** The paper prints $\sum_a X_{ak}e_{U,k}$ in the displayed definition of $w_k$, a slip for $e_{U,a}$ (the preceding line has $w_{U,k}=\sum_a X_{ak}e_{U,a}$); the statement uses $e_{U,a}$. The $\underline\xi_k$ are elements of $D_{f^+}$ that lie in `f.closure.domain`. Clause 1 is the equality `cutOut f w = cutOut f (eU …)` of operators. $z=i$ throughout.
--   **Formalization Note** $H$ is a complex Hilbert space (`InnerProductSpace ℂ H`, `CompleteSpace H`); operators are `LinearPMap`s $H\to H$, with Mathlib's adjoint `f.adjoint` and closure `f.closure`. Mathlib's inner product is conjugate-linear in the first argument, as in the paper. Symmetry is the published `TeschlQM.Shared.IsSymmetric` (densely defined and $(\eta,f\xi)=(f\eta,\xi)$ on $D_f$).
-- source:
--   Voronov, Gitman & Tyutin, Self-adjoint differential operators assosiated with self-adjoint differential expressions, arXiv:quant-ph/0603187v2, p. 66, eqs. (142)–(143)

import Mathlib
import Definitions.Def_TeschlQM_Shared_IsSymmetric
import Definitions.Def_TeschlQM_SelfAdjoint_addScalar
import Definitions.Def_VoronovSA_AsymExt_AsymForm

namespace VoronovSA.AsymExt

open scoped InnerProductSpace
open TeschlQM.SelfAdjoint

/-- Voronov–Gitman–Tyutin (142)–(143), Sec. 3.7, p. 66: for a unitary `U`, a nonsingular `m × m`
matrix `X` and vectors `ξ_k ∈ D_{f̄}`, the vectors `w_k = ∑_a X_{ak} e_{U,a} + ξ_k` cut out the same
self-adjoint extension as the `e_{U,k}` (142), satisfy `ω*(w_k, w_l) = 0` (143), and are linearly
independent modulo `D_{f̄}`. -/
theorem eq_142_143 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (f : H →ₗ.[ℂ] H) (hf : TeschlQM.Shared.IsSymmetric f) (m : ℕ) (hm : 0 < m)
    (eP : OrthonormalBasis (Fin m) ℂ (kerAdd f.adjoint (-Complex.I)))
    (eM : OrthonormalBasis (Fin m) ℂ (kerAdd f.adjoint Complex.I))
    (U : Matrix (Fin m) (Fin m) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin m) ℂ)
    (X : Matrix (Fin m) (Fin m) ℂ) (hX : X.det ≠ 0)
    (ξ : Fin m → f.adjoint.domain) (hξ : ∀ k, (ξ k : H) ∈ f.closure.domain) :
    cutOut f (fun k => ∑ a, X a k • eU f eP eM U a + ξ k) = cutOut f (eU f eP eM U) ∧
      (∀ k l, asymForm f (∑ a, X a k • eU f eP eM U a + ξ k)
        (∑ a, X a l • eU f eP eM U a + ξ l) = 0) ∧
      LinIndepModClosure f (fun k => ∑ a, X a k • eU f eP eM U a + ξ k) := by sorry

end VoronovSA.AsymExt
