-- Prove2me | Theorems.Thm_VoronovSA_AsymExt_theorem_3_unitary_parametrization
-- name    : VoronovSA.AsymExt.theorem_3_unitary_parametrization
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:23:18.669614+00:00
-- url     : https://prove2.me/theorems/d09c60d1-ec80-45cb-a90a-ea1319dbdb7b
-- title:
--   Theorem 3, (33)–(35) — for finite indices m > 0 the s.a. extensions are exactly f̂_U, U ∈ U(m), cut out by ω*(e_{U,k}, ·) = 0
-- statement:
--   Let $\hat f$ be a symmetric operator in a complex Hilbert space $\mathcal H$ with closure $\bar f$ and adjoint $\hat f^{+}$. Assume that its deficient subspaces $D_+=\ker(\hat f^+-i)$ and $D_-=\ker(\hat f^++i)$ both have finite dimension $m>0$, and fix orthonormal bases $\{e_{+,k}\}_{k=1}^m$ of $D_+$ and $\{e_{-,l}\}_{l=1}^m$ of $D_-$. For an $m\times m$ matrix $U$ put $e_{U,k}=e_{+,k}+\sum_{l}U_{lk}e_{-,l}$ and let $\hat f_U$ be the restriction of $\hat f^{+}$ to
--   $$D_{f_U}=\{\xi_U\in D_{f^+}:\ \omega_*(e_{U,k},\xi_U)=0,\ k=1,\dots,m\}\qquad(35)$$
--   Then:
--
--   1. for every unitary $U\in U(m)$, $\hat f_U$ is a self-adjoint extension of $\hat f$, its domain is
--   $$D_{f_U}=\Big\{\underline\xi+\sum_{k=1}^m c_k e_{U,k}:\ \underline\xi\in D_{\bar f},\ c_k\in\mathbb C\Big\},\qquad(33)$$
--   and on it
--   $$\hat f_U\Big(\underline\xi+\sum_k c_k e_{U,k}\Big)=\bar f\underline\xi+\sum_{k=1}^m c_k\Big(i\,e_{+,k}-i\sum_{l=1}^m U_{lk}e_{-,l}\Big);\qquad(34)$$
--   2. every self-adjoint extension of $\hat f$ equals $\hat f_U$ for some unitary $U$;
--   3. distinct unitaries give distinct extensions, so with the bases fixed the self-adjoint extensions are parametrized by the unitary group $U(m)$.
--
--   This is the finite-index part of the paper's "main theorem", the classical von Neumann parametrization written as a restriction of the adjoint. Theorem 15 replaces the vectors $e_{U,k}$, which require the deficient subspaces, with arbitrary vectors of $D_{f^+}$.
--
--   **Formalization Note** The paper states Theorem 3 for an arbitrary $z$ in the upper half-plane; this item fixes $z=i$ (the paper's convention $z=i\kappa$ of p. 23, with $\kappa=1$), so $\bar z=-i$ in (34). The dimension $m$ is carried by orthonormal bases indexed by `Fin m` (`OrthonormalBasis (Fin m) ℂ (kerAdd f.adjoint (∓I))`), which forces both deficiency indices to equal $m$. $U(m)$ is `Matrix.unitaryGroup (Fin m) ℂ`. $\hat f_U$ is `cutOut f (eU f eP eM U)`, self-adjointness is Mathlib's `IsSelfAdjoint` (`g† = g`, domains included), and "extension" is `f ≤ g`. In (33) the span of the $e_{U,k}$ is added to `f.closure.domain`. The paper's "$\xi_U\subset D_{f^+}$" in (35) is read as $\in$.
--   **Formalization Note** $H$ is a complex Hilbert space (`InnerProductSpace ℂ H`, `CompleteSpace H`); operators are `LinearPMap`s $H\to H$, with Mathlib's adjoint `f.adjoint` and closure `f.closure`. Mathlib's inner product is conjugate-linear in the first argument, as in the paper. Symmetry is the published `TeschlQM.Shared.IsSymmetric` (densely defined and $(\eta,f\xi)=(f\eta,\xi)$ on $D_f$).
-- source:
--   Voronov, Gitman & Tyutin, Self-adjoint differential operators assosiated with self-adjoint differential expressions, arXiv:quant-ph/0603187v2, pp. 19–20, Theorem 3, eqs. (33)–(35) (and p. 19, 'the manifold U(m)')

import Mathlib
import Definitions.Def_TeschlQM_Shared_IsSymmetric
import Definitions.Def_TeschlQM_SelfAdjoint_addScalar
import Definitions.Def_VoronovSA_AsymExt_AsymForm

namespace VoronovSA.AsymExt

open scoped InnerProductSpace
open TeschlQM.SelfAdjoint

/-- Voronov–Gitman–Tyutin, Theorem 3, (33)–(35), p. 20, at `z = i`. Let `f` be symmetric with
finite deficiency indices `m₊ = m₋ = m > 0`, given by orthonormal bases `e_{+,k}` of
`D₊ = Ker(f⁺ − i)` and `e_{−,l}` of `D₋ = Ker(f⁺ + i)`, and let `e_{U,k} = e_{+,k} + ∑_l U_{lk} e_{−,l}`.
(i) For every unitary `U ∈ U(m)`, the operator `f̂_U` cut out of `f⁺` by `ω*(e_{U,k}, ·) = 0` (35) is a
self-adjoint extension of `f`, its domain is `D_{f̄} + span{e_{U,k}}` (33), and it acts by
`f̂_U(ξ + ∑ c_k e_{U,k}) = f̄ξ + ∑ c_k (i e_{+,k} − i ∑_l U_{lk} e_{−,l})` (34).
(ii) Every self-adjoint extension of `f` is such an `f̂_U` for some unitary `U`.
(iii) Distinct unitaries give distinct extensions (p. 19: the family `{f̂_U}` "is the manifold `U(m)`"). -/
theorem theorem_3_unitary_parametrization {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (f : H →ₗ.[ℂ] H) (hf : TeschlQM.Shared.IsSymmetric f) (m : ℕ) (hm : 0 < m)
    (eP : OrthonormalBasis (Fin m) ℂ (kerAdd f.adjoint (-Complex.I)))
    (eM : OrthonormalBasis (Fin m) ℂ (kerAdd f.adjoint Complex.I)) :
    (∀ U ∈ Matrix.unitaryGroup (Fin m) ℂ,
        f ≤ cutOut f (eU f eP eM U) ∧ IsSelfAdjoint (cutOut f (eU f eP eM U)) ∧
        (cutOut f (eU f eP eM U)).domain =
          f.closure.domain ⊔ Submodule.span ℂ (Set.range fun k => (eU f eP eM U k : H)) ∧
        ∀ (ξ : f.closure.domain) (c : Fin m → ℂ)
          (h : (ξ : H) + ∑ k, c k • (eU f eP eM U k : H) ∈ (cutOut f (eU f eP eM U)).domain),
          cutOut f (eU f eP eM U) ⟨(ξ : H) + ∑ k, c k • (eU f eP eM U k : H), h⟩ =
            f.closure ξ + ∑ k, c k • (Complex.I • (eP k : H) +
              (-Complex.I) • ∑ l, U l k • (eM l : H))) ∧
      (∀ g : H →ₗ.[ℂ] H, f ≤ g → IsSelfAdjoint g →
        ∃ U ∈ Matrix.unitaryGroup (Fin m) ℂ, g = cutOut f (eU f eP eM U)) ∧
      (∀ U ∈ Matrix.unitaryGroup (Fin m) ℂ, ∀ V ∈ Matrix.unitaryGroup (Fin m) ℂ,
        cutOut f (eU f eP eM U) = cutOut f (eU f eP eM V) → U = V) := by sorry

end VoronovSA.AsymExt
