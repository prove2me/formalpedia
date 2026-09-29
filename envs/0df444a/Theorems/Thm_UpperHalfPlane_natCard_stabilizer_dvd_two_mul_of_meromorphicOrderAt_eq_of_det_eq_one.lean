-- Prove2me | Theorems.Thm_UpperHalfPlane_natCard_stabilizer_dvd_two_mul_of_meromorphicOrderAt_eq_of_det_eq_one
-- name    : UpperHalfPlane.natCard_stabilizer_dvd_two_mul_of_meromorphicOrderAt_eq_of_det_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/bcf1d033-91fd-5321-98b8-bae3fad25c32
-- title:
--   Stabiliser order divides twice the meromorphic order at τ
-- statement:
--   Let $\Gamma$ be a subgroup of $\mathrm{GL}_2(\mathbb R)$ all of whose elements have determinant $1$ (so that $\Gamma$ acts on the upper half plane $\mathbb H$ by the Möbius transformations $z \mapsto (az+b)/(cz+d)$), let $F : \mathbb H \to \mathbb C$ be a function and let $\tau \in \mathbb H$. Assume that $F$ is invariant near $\tau$ under the elements of $\Gamma$ fixing $\tau$, in the germ sense: for every $\gamma \in \Gamma$ with $\gamma \cdot \tau = \tau$, the identity $F(\gamma \cdot z) = F(z)$ holds for all $z$ in some punctured neighbourhood of $\tau$ in $\mathbb H$ (i.e. eventually along the filter $\mathcal N[\neq]\,\tau$). Assume further that for an integer $n$ the function $z \mapsto F(\mathrm{ofComplex}\ z)$ on $\mathbb C$, where `UpperHalfPlane.ofComplex` is the retraction of $\mathbb C$ onto $\mathbb H$ that is the identity on $\mathbb H$, has meromorphic order exactly $n$ at the point $\tau \in \mathbb C$; since `meromorphicOrderAt` takes values in $\mathbb Z \cup \{\infty\}$, this in particular excludes the germ being zero. The conclusion is that the cardinality of the stabiliser of $\tau$ in $\Gamma$, as an integer, divides $2n$. If that stabiliser is infinite its `Nat.card` is $0$, and the conclusion then forces $n = 0$.
--
--   This is the standard divisibility constraint at an elliptic point: the order of vanishing (or pole) of a $\Gamma$-invariant germ at $\tau$ is a multiple of the order of the isotropy group, up to the factor $2$ coming from $\pm 1$. It is stated here for arbitrary determinant-one subgroups of $\mathrm{GL}_2(\mathbb R)$ — in particular for the Fuchsian groups arising from quaternion orders — and only with invariance of germs at $\tau$; it is used in the construction of local parameters and of separating functions on modular curves, by [`ModularCurve.exists_modularForm_separate_and_localParameter_of_discreteTopology`](thm.html#ModularCurve.exists_modularForm_separate_and_localParameter_of_discreteTopology) and [`ModularCurve.exists_placeDictionary_automorphicField_of_discreteTopology`](thm.html#ModularCurve.exists_placeDictionary_automorphicField_of_discreteTopology).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_UpperHalfPlane_natCard_stabilizer_dvd_two_mul_of_meromorphicOrderAt_eq_of_det_eq_one.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Filter UpperHalfPlane
open scoped MatrixGroups Topology

theorem UpperHalfPlane.natCard_stabilizer_dvd_two_mul_of_meromorphicOrderAt_eq_of_det_eq_one
    (Γ : Subgroup (GL (Fin 2) ℝ)) (hdet : ∀ γ ∈ Γ, Matrix.GeneralLinearGroup.det γ = 1)
    (F : ℍ → ℂ) (τ : ℍ)
    (hF : ∀ γ ∈ Γ, γ • τ = τ → ∀ᶠ z in 𝓝[≠] τ, F (γ • z) = F z)
    (n : ℤ) (hn : meromorphicOrderAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ) = n) :
    (Nat.card (MulAction.stabilizer Γ τ) : ℤ) ∣ 2 * n := by sorry
