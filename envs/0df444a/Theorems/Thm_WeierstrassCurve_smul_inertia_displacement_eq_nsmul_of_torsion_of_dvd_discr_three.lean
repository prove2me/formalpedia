-- Prove2me | Theorems.Thm_WeierstrassCurve_smul_inertia_displacement_eq_nsmul_of_torsion_of_dvd_discr_three
-- name    : WeierstrassCurve.smul_inertia_displacement_eq_nsmul_of_torsion_of_dvd_discr_three
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/87753c67-9312-5f99-8e55-0a77f26699d3
-- title:
--   Inertia acts on 3-torsion displacements through ω at 3
-- statement:
--   Let $W$ be a Weierstrass curve over $\mathbb{Z}$ with $\Delta \ne 0$, satisfying $3 \mid \Delta$ and $3 \nmid c_4$, and suppose that the group of $3$-torsion points of $W$ base-changed along $\mathbb{Z} \to \mathbb{Q}$ and then to $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` — that is, the $\mathbb{Z}$-submodule killed by $3$ inside the projective point group of the curve over $\overline{\mathbb{Q}}$ — has exactly $3^2 = 9$ elements. Write $I$ for the inertia subgroup inside $\operatorname{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ attached to the place [`padicPlace 3`](def/GaloisRep_CompletionBridge.html#L25) of $\overline{\mathbb{Q}}$, namely the valuation subring obtained by pulling back the valuation subring of $\overline{\mathbb{Q}}_3$ along a fixed embedding $\overline{\mathbb{Q}} \hookrightarrow \overline{\mathbb{Q}}_3$; concretely $I$ is the image, under the inclusion of the decomposition subgroup into the full Galois group, of the inertia subgroup of that place over $\mathbb{Q}$. The assertion is: for every $\sigma \in I$ and every natural number $c$ such that $\sigma(\zeta) = \zeta^c$ for all $\zeta \in \overline{\mathbb{Q}}$ with $\zeta^3 = 1$, for every $\tau \in I$ and every point $y$ of the curve over $\overline{\mathbb{Q}}$ with $3y = 0$, one has $\sigma \cdot (\tau \cdot y - y) = c\,(\tau \cdot y - y)$.
--
--   This is the statement, at the prime $3$ and for the $3$-adic place, that at a prime of multiplicative reduction the inertia action on $E[3]$ has the shape $\begin{pmatrix}\omega & *\\ 0 & 1\end{pmatrix}$: the displacements $\tau y - y$ of $3$-torsion points under inertia lie in the line on which inertia acts by the mod-$3$ cyclotomic character. It feeds the analysis of the residual representation at $3$ of a curve which is not finite flat there, used in the ramification conditions on the mod-$3$ representation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_smul_inertia_displacement_eq_nsmul_of_torsion_of_dvd_discr_three.lean

import Mathlib
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_CompletionBridge

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped WeierstrassCurve.Affine
open WeierstrassCurve.Affine WeierstrassCurve.Affine.Point
open WeierstrassCurve

theorem WeierstrassCurve.smul_inertia_displacement_eq_nsmul_of_torsion_of_dvd_discr_three
    (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0)
    (hpΔ : (3 : ℤ) ∣ W.Δ) (hpc₄ : ¬ (3 : ℤ) ∣ W.c₄)
    (hcard : Nat.card (Submodule.torsionBy ℤ
      ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point 3) = 3 ^ 2) :
    ∀ σ ∈ (padicPlace 3).inertiaSubgroupIn ℚ, ∀ c : ℕ,
      (∀ ζ : AlgebraicClosure ℚ, ζ ^ 3 = 1 → σ ζ = ζ ^ c) →
      ∀ τ ∈ (padicPlace 3).inertiaSubgroupIn ℚ,
        ∀ y : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point,
          (3 : ℤ) • y = 0 → σ • (τ • y - y) = (c : ℤ) • (τ • y - y) := by sorry
