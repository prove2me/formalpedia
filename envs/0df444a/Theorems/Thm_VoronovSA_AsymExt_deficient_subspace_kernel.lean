-- Prove2me | Theorems.Thm_VoronovSA_AsymExt_deficient_subspace_kernel
-- name    : VoronovSA.AsymExt.deficient_subspace_kernel
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:23:18.296277+00:00
-- url     : https://prove2.me/theorems/566d29cd-a018-4883-9e15-b6dcf160d236
-- title:
--   Sec. 2.2 — the deficient subspace ℵ_z = (R_{f−zI})⊥ = (R_{f̄−zI})⊥ = ker(f⁺ − z̄)
-- statement:
--   Let $\hat f$ be a symmetric operator in a complex Hilbert space $\mathcal H$, with closure $\bar f$ and adjoint $\hat f^{+}$, and let $z\in\mathbb C$ with $\operatorname{Im}z\neq0$. The deficient subspace $\aleph_z$ can be written equivalently as the orthogonal complement of the range of $\hat f-z$, as the orthogonal complement of the range of $\bar f-z$, or as an eigenspace of the adjoint:
--   $$\aleph_z=(R_{f-zI})^{\perp}=(R_{\bar f-zI})^{\perp}=\ker(\hat f^{+}-\bar z\hat I)=\{\xi\in D_{f^+}:\ \hat f^{+}\xi=\bar z\xi\}.$$
--
--   The paper defines the deficient subspaces as range complements and works with them as eigenspaces of $\hat f^{+}$. This identity links the two descriptions, and with them the range form used by the published defect spaces to the kernel form used in this mission.
--
--   **Formalization Note** `rangeAdd f (-z)` is $\{f\psi-z\psi:\psi\in D_f\}$ and `kerAdd f.adjoint (-(conj z))` is $\{\psi\in D_{f^+}: f^+\psi-\bar z\psi=0\}$, both from the published `TeschlQM.SelfAdjoint.addScalar` module; `ᗮ` is the orthogonal complement in $H$.
--   **Formalization Note** $H$ is a complex Hilbert space (`InnerProductSpace ℂ H`, `CompleteSpace H`); operators are `LinearPMap`s $H\to H$, with Mathlib's adjoint `f.adjoint` and closure `f.closure`. Mathlib's inner product is conjugate-linear in the first argument, as in the paper. Symmetry is the published `TeschlQM.Shared.IsSymmetric` (densely defined and $(\eta,f\xi)=(f\eta,\xi)$ on $D_f$).
-- source:
--   Voronov, Gitman & Tyutin, Self-adjoint differential operators assosiated with self-adjoint differential expressions, arXiv:quant-ph/0603187v2, p. 8, Sec. 2.2 (display defining ℵ_z)

import Mathlib
import Definitions.Def_TeschlQM_Shared_IsSymmetric
import Definitions.Def_TeschlQM_SelfAdjoint_addScalar
import Definitions.Def_VoronovSA_AsymExt_AsymForm

namespace VoronovSA.AsymExt

open scoped InnerProductSpace
open TeschlQM.SelfAdjoint

/-- Voronov–Gitman–Tyutin, Sec. 2.2, p. 8: for a symmetric operator `f` and `z ∉ ℝ`, the deficient
subspace `ℵ_z = (R_{f−zI})^⊥ = (R_{f̄−zI})^⊥ = ker(f⁺ − z̄)`. Here `rangeAdd f (-z) = Ran(f − z)`
and `kerAdd f.adjoint (-(conj z)) = Ker(f⁺ − z̄)`. -/
theorem deficient_subspace_kernel {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (f : H →ₗ.[ℂ] H) (hf : TeschlQM.Shared.IsSymmetric f) (z : ℂ) (hz : z.im ≠ 0) :
    (rangeAdd f (-z))ᗮ = (rangeAdd f.closure (-z))ᗮ ∧
      (rangeAdd f (-z))ᗮ = kerAdd f.adjoint (-(starRingEnd ℂ z)) := by sorry

end VoronovSA.AsymExt
