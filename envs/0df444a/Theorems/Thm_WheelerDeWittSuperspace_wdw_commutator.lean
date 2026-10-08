-- Prove2me | Theorems.Thm_WheelerDeWittSuperspace_wdw_commutator
-- name    : WheelerDeWittSuperspace.wdw_commutator
-- status  : Open
-- author  : @Mazecto
-- created : 2026-10-05T22:47:32.44773+00:00
-- url     : https://prove2.me/theorems/be93b718-7398-4a66-8065-1d48cb161664
-- title:
--   Commutator of two lattice Wheeler–DeWitt constraints
-- statement:
--   Let $V_z(h)=-\tfrac{\sqrt{\det h(z)}}{2\kappa}(R(h,z)-2\Lambda)$ with each $R(\cdot,z)$ of class $C^2$, let $\Psi$ be $C^4$, let $h$ be physical and $x\neq y$. Then
--   $$[\widehat{\mathcal H}_x,\widehat{\mathcal H}_y]\Psi=-2\kappa\hbar^2\Big(G_{abcd}(h(x))\big(2\,\partial^{x}_{ab}V_y\,\partial^{x}_{cd}\Psi+\partial^{x}_{ab}\partial^{x}_{cd}V_y\,\Psi\big)-(x\leftrightarrow y)\Big),$$
--   with $\partial^{x}_{ab}=\partial/\partial h_{ab}(x)$. The commutator is a first-order operator whose coefficients measure how the potential at one site depends on the metric at the other.
-- source:
--   R. Loll, Discrete approaches to quantum gravity in four dimensions, Living Rev. Relativ. 1 (1998), Section 2.12, https://arxiv.org/abs/gr-qc/9805049; B. Dittrich, https://arxiv.org/abs/0810.3594, p. 6; B. Bahr, B. Dittrich, https://arxiv.org/abs/0905.1670; M. Bander, Phys. Rev. D 36 (1987) 2297

import Definitions.Def_WheelerDeWittSuperspace

set_option autoImplicit false

open Matrix

namespace WheelerDeWittSuperspace

/-- Milestone 6 (quantum lattice commutator): two lattice Wheeler–DeWitt constraints
fail to commute by an explicit first-order operator built from the cross-derivatives
of the potentials. -/
theorem wdw_commutator {X : Type*} [Fintype X] [DecidableEq X] (kappa hbar Lam : ℝ)
    (hkappa : kappa ≠ 0) (hhbar : hbar ≠ 0)
    (R : Config X → X → ℝ) (hR : ∀ z, ContDiff ℝ 2 (fun h => R h z))
    (Ψ : Config X → ℂ) (hΨ : ContDiff ℝ 4 Ψ) (h : Config X) (hh : IsPhysical h)
    (x y : X) (hxy : x ≠ y) :
    wdw kappa hbar Lam R (fun h' => wdw kappa hbar Lam R Ψ h' y) h x -
      wdw kappa hbar Lam R (fun h' => wdw kappa hbar Lam R Ψ h' x) h y =
    -2 * (kappa : ℂ) * (hbar : ℂ) ^ 2 *
      ((∑ a, ∑ b, ∑ c, ∑ d, (deWitt (metricAt h x) a b c d : ℂ) *
          (2 * (partialR (fun h' => potentialAt kappa Lam R h' y) x a b h : ℂ) *
              partialD Ψ x c d h +
            (partialR (partialR (fun h' => potentialAt kappa Lam R h' y) x c d) x a b h : ℂ) *
              Ψ h)) -
       (∑ a, ∑ b, ∑ c, ∑ d, (deWitt (metricAt h y) a b c d : ℂ) *
          (2 * (partialR (fun h' => potentialAt kappa Lam R h' x) y a b h : ℂ) *
              partialD Ψ y c d h +
            (partialR (partialR (fun h' => potentialAt kappa Lam R h' x) y c d) y a b h : ℂ) *
              Ψ h))) := by sorry

end WheelerDeWittSuperspace
