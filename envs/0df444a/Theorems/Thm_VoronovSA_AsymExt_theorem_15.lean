-- Prove2me | Theorems.Thm_VoronovSA_AsymExt_theorem_15
-- name    : VoronovSA.AsymExt.theorem_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:23:19.025452+00:00
-- url     : https://prove2.me/theorems/a23cfc1f-39d6-4a8a-af17-9aef7e28bbd0
-- title:
--   Theorem 15 — the s.a. extensions of f are exactly the restrictions of f⁺ cut out by ω*(w_k, ·) = 0 for isotropic w_k independent mod D_f̄
-- statement:
--   Let $\hat f$ be a symmetric operator in a complex Hilbert space $\mathcal H$, with closure $\bar f$ and adjoint $\hat f^{+}$, and let
--   $$\omega_*(\eta_*,\xi_*)=(\eta_*,\hat f^{+}\xi_*)-(\hat f^{+}\eta_*,\xi_*),\qquad \eta_*,\xi_*\in D_{f^+},$$
--   be the asymmetry form of the adjoint. Assume the deficiency indices are equal, finite and nonzero:
--   $$m_+=\dim\ker(\hat f^{+}-i)=m_-=\dim\ker(\hat f^{+}+i)=m>0 .$$
--   For vectors $w_1,\dots,w_m\in D_{f^+}$ let $\hat f_U$ be the operator
--   $$\hat f_U:\quad D_{f_U}=\{\psi_U\in D_{f^+}:\ \omega_*(w_k,\psi_U)=0,\ k=1,\dots,m\},\qquad \hat f_U\psi_U=\hat f^{+}\psi_U .\qquad(144)$$
--   Then:
--
--   1. every self-adjoint extension of $\hat f$ is of the form (144) for some $w_1,\dots,w_m\in D_{f^+}$ that are linearly independent modulo $D_{\bar f}$ ($\sum_kc_kw_k\in D_{\bar f}\Rightarrow c=0$) and satisfy
--   $$\omega_*(w_k,w_l)=0,\qquad k,l=1,\dots,m;\qquad(143)$$
--   2. conversely, for any $w_1,\dots,w_m\in D_{f^+}$ that are linearly independent modulo $D_{\bar f}$ and satisfy (143), the operator (144) is a self-adjoint extension of $\hat f$.
--
--   The theorem describes all self-adjoint extensions of $\hat f$ by $m$ linear conditions on $D_{f^+}$. Unlike von Neumann's parametrization by unitary maps between the deficient subspaces, it does not require those subspaces to be computed. For differential operators it becomes the description of self-adjoint boundary conditions by boundary forms (Theorem 16 of the paper).
--
--   **Formalization Note** The deficiency indices are taken at $z=i$, as the dimensions (`Module.finrank`) of `kerAdd f.adjoint (-I)` $=\ker(f^+-i)$ and `kerAdd f.adjoint I` $=\ker(f^++i)$. Since `finrank` is $0$ on infinite-dimensional spaces, the hypothesis $m>0$ also makes both indices finite; the paper's statement leaves finiteness implicit, and its proof uses $m\times m$ matrices. The form $\omega_*$ does not depend on $z$. Families are indexed by `Fin m`. Linear independence is modulo `f.closure.domain`. The operator (144) is `cutOut f w`, the restriction of `f.adjoint` to the annihilator. "Self-adjoint extension" is `f ≤ g ∧ IsSelfAdjoint g` with Mathlib's `IsSelfAdjoint` ($g^\dagger=g$, domains included), which covers the paper's chain $\hat f\subseteq\bar f\subset\hat f_U=\hat f_U^{+}\subset\hat f^{+}$.
--   **Formalization Note** $H$ is a complex Hilbert space (`InnerProductSpace ℂ H`, `CompleteSpace H`); operators are `LinearPMap`s $H\to H$, with Mathlib's adjoint `f.adjoint` and closure `f.closure`. Mathlib's inner product is conjugate-linear in the first argument, as in the paper. Symmetry is the published `TeschlQM.Shared.IsSymmetric` (densely defined and $(\eta,f\xi)=(f\eta,\xi)$ on $D_f$).
-- source:
--   Voronov, Gitman & Tyutin, Self-adjoint differential operators assosiated with self-adjoint differential expressions, arXiv:quant-ph/0603187v2, p. 68, Theorem 15, eqs. (143)–(144); proof pp. 65–68

import Mathlib
import Definitions.Def_TeschlQM_Shared_IsSymmetric
import Definitions.Def_TeschlQM_SelfAdjoint_addScalar
import Definitions.Def_VoronovSA_AsymExt_AsymForm

namespace VoronovSA.AsymExt

open scoped InnerProductSpace
open TeschlQM.SelfAdjoint

/-- Voronov–Gitman–Tyutin, Theorem 15 (addition to the main theorem), p. 68. Let `f` be a symmetric
operator whose deficiency indices are equal and finite, `m₊ = dim Ker(f⁺ − i) = m₋ = dim Ker(f⁺ + i) = m > 0`.
(a) Every self-adjoint extension `g` of `f` is `f⁺` restricted to
`{ψ ∈ D_{f⁺} : ω*(w_k, ψ) = 0, k = 1, …, m}` (144) for some `w_1, …, w_m ∈ D_{f⁺}` that are linearly
independent modulo `D_{f̄}` and satisfy `ω*(w_k, w_l) = 0` (143).
(b) Conversely, every such family defines by (144) a self-adjoint extension of `f`. -/
theorem theorem_15 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (f : H →ₗ.[ℂ] H) (hf : TeschlQM.Shared.IsSymmetric f) (m : ℕ) (hm : 0 < m)
    (hplus : Module.finrank ℂ (kerAdd f.adjoint (-Complex.I)) = m)
    (hminus : Module.finrank ℂ (kerAdd f.adjoint Complex.I) = m) :
    (∀ g : H →ₗ.[ℂ] H, f ≤ g → IsSelfAdjoint g →
        ∃ w : Fin m → f.adjoint.domain, LinIndepModClosure f w ∧
          (∀ k l, asymForm f (w k) (w l) = 0) ∧ g = cutOut f w) ∧
      (∀ w : Fin m → f.adjoint.domain, LinIndepModClosure f w →
        (∀ k l, asymForm f (w k) (w l) = 0) → f ≤ cutOut f w ∧ IsSelfAdjoint (cutOut f w)) := by sorry

end VoronovSA.AsymExt
