-- Prove2me | Theorems.Thm_VoronovSA_AsymExt_eq_141
-- name    : VoronovSA.AsymExt.eq_141
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:23:26.838545+00:00
-- url     : https://prove2.me/theorems/1cb19c5c-8e22-4a34-af05-4506907ebdf8
-- title:
--   (141) — the vectors e_{U,k} are linearly independent modulo D_f̄ and satisfy ω*(e_{U,k}, e_{U,l}) = 0
-- statement:
--   Let $\hat f$ be a symmetric operator in a complex Hilbert space $\mathcal H$ whose deficient subspaces $D_+=\ker(\hat f^+-i)$ and $D_-=\ker(\hat f^++i)$ have orthonormal bases $\{e_{+,k}\}_{k=1}^m$ and $\{e_{-,l}\}_{l=1}^m$, $m>0$. For a unitary $m\times m$ matrix $U$ let $e_{U,k}=e_{+,k}+\sum_l U_{lk}e_{-,l}$. Then:
--
--   1. the vectors $e_{U,1},\dots,e_{U,m}$ are linearly independent modulo $D_{\bar f}$;
--   2. they are mutually $\omega_*$-isotropic:
--   $$\omega_*(e_{U,k},e_{U,l})=0,\qquad k,l=1,\dots,m.\qquad(141)$$
--
--   These two properties are what the family $\{e_{U,k}\}$ shares with the general families $\{w_k\}$ of Theorem 15. They begin the proof that every self-adjoint extension has the form (144).
--
--   **Formalization Note** The vectors are `eU f eP eM U`; linear independence modulo $D_{\bar f}$ is `LinIndepModClosure`. $z=i$ throughout.
--   **Formalization Note** $H$ is a complex Hilbert space (`InnerProductSpace ℂ H`, `CompleteSpace H`); operators are `LinearPMap`s $H\to H$, with Mathlib's adjoint `f.adjoint` and closure `f.closure`. Mathlib's inner product is conjugate-linear in the first argument, as in the paper. Symmetry is the published `TeschlQM.Shared.IsSymmetric` (densely defined and $(\eta,f\xi)=(f\eta,\xi)$ on $D_f$).
-- source:
--   Voronov, Gitman & Tyutin, Self-adjoint differential operators assosiated with self-adjoint differential expressions, arXiv:quant-ph/0603187v2, p. 65, eq. (141)

import Mathlib
import Definitions.Def_TeschlQM_Shared_IsSymmetric
import Definitions.Def_TeschlQM_SelfAdjoint_addScalar
import Definitions.Def_VoronovSA_AsymExt_AsymForm

namespace VoronovSA.AsymExt

open scoped InnerProductSpace
open TeschlQM.SelfAdjoint

/-- Voronov–Gitman–Tyutin (141), Sec. 3.7, p. 65: for a unitary `U`, the vectors
`e_{U,k} = e_{+,k} + ∑_l U_{lk} e_{−,l}` of (37) are linearly independent modulo `D_{f̄}` and satisfy
`ω*(e_{U,k}, e_{U,l}) = 0` for all `k, l`. -/
theorem eq_141 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (f : H →ₗ.[ℂ] H) (hf : TeschlQM.Shared.IsSymmetric f) (m : ℕ) (hm : 0 < m)
    (eP : OrthonormalBasis (Fin m) ℂ (kerAdd f.adjoint (-Complex.I)))
    (eM : OrthonormalBasis (Fin m) ℂ (kerAdd f.adjoint Complex.I))
    (U : Matrix (Fin m) (Fin m) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin m) ℂ) :
    LinIndepModClosure f (eU f eP eM U) ∧
      ∀ k l, asymForm f (eU f eP eM U k) (eU f eP eM U l) = 0 := by sorry

end VoronovSA.AsymExt
