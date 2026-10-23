-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P42_rayHamiltonian_characterization
-- name    : QAlgorithms.Papers.Independent.Renew46.P42.rayHamiltonian_characterization
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T21:21:27.535589+00:00
-- url     : https://prove2.me/theorems/d4cf3ad8-6fd4-47ea-b092-4ab8e2a94ea5
-- title:
--   Ray Hamiltonian, comoving speed, and wave-number independence
-- statement:
--   Work in the nondispersive geometrical-optics model. Let $c>0$, $n\ge1$, $\mathbf u\cdot\mathbf u<c^2$, and $\mathbf k\ne0$. Write $k=|\mathbf k|$, $\mathbf e=\mathbf k/k$, $\gamma=(1-|\mathbf u|^2/c^2)^{-1/2}$,
--   $A=(n^2-1)c^2/(n^2c^2-|\mathbf u|^2)$, and $B=\sqrt{(c^2-|\mathbf u|^2)/(n^2c^2-|\mathbf u|^2)}$. Construct
--
--   $$H(\mathbf k)=B\sqrt{c^2k^2-A(\mathbf u\cdot\mathbf k)^2}+A\mathbf u\cdot\mathbf k.$$
--
--   This is the unique root of $D(\omega)=\omega^2-c^2k^2+(n^2-1)\gamma^2(\omega-\mathbf u\cdot\mathbf k)^2$ with $\omega-\mathbf u\cdot\mathbf k>0$. At rest it is $ck/n$. For $\mathbf v=\partial_{\mathbf k}H$, the Lorentz-transformed velocity $\mathbf v'$ has $|\mathbf v'|^2=c^2/n^2$, using $\mathbf v'=\mathbf v$ at $\mathbf u=0$. Put $h(\zeta)=B\sqrt{c^2-A\zeta^2}+A\zeta$. Then $H=k h(\mathbf u\cdot\mathbf e)$ and $\mathbf v=h\mathbf e+h'\mathbf e\times(\mathbf u\times\mathbf e)$. For every $a>0$, $H(a\mathbf k)=aH(\mathbf k)$ and $\mathbf v(a\mathbf k)=\mathbf v(\mathbf k)$.
--
--   These identities fix the Hamiltonian branch and the physical laboratory time and show that ray speed is independent of wave number.
-- source:
--   Optics of Nonuniformly Moving Media, arXiv:physics/9906038v3, PDF p. 5, §III B, (30)–(38): ray Hamiltonian, comoving speed and independence of wave number

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P42

namespace QAlgorithms.Papers.Independent.Renew46.P42

noncomputable section

open scoped BigOperators

open Filter Set MeasureTheory

-- Reuse the pinned accepted real quadratic form (arbitrary finite real matrices).

open QAlgorithms.Papers.Independent.Information100.P37 (quadratic)

/-- PDF pp.4–5, (30)–(38): constructed ray Hamiltonian, physical comoving speed,
and independence of wave number. Laboratory frequency is not assumed positive. -/
theorem rayHamiltonian_characterization (c n : ℝ) (u k : V3)
    (hc : 0 < c) (hn : 1 ≤ n) (hu : dot3 u u < c ^ 2) (hk : k ≠ 0) :
    rayDispersion c n u k (rayHamiltonian c n u k) = 0 ∧
    (∀ omega : ℝ, (rayDispersion c n u k omega = 0 ∧ 0 < omega - dot3 u k) ↔
      omega = rayHamiltonian c n u k) ∧
    rayHamiltonian c n 0 k = c * length3 k / n ∧
    dot3 (comovingVelocity c u (rayVelocity c n u k))
      (comovingVelocity c u (rayVelocity c n u k)) = c ^ 2 / n ^ 2 ∧
    rayHamiltonian c n u k = length3 k *
      directionalH c n u (dot3 u ((1 / length3 k) • k)) ∧
    rayVelocity c n u k =
      directionalH c n u (dot3 u ((1 / length3 k) • k)) • ((1 / length3 k) • k) +
      deriv (directionalH c n u) (dot3 u ((1 / length3 k) • k)) •
        cross3 ((1 / length3 k) • k) (cross3 u ((1 / length3 k) • k)) ∧
    (∀ a : ℝ, 0 < a →
      rayHamiltonian c n u (a • k) = a * rayHamiltonian c n u k ∧
      rayVelocity c n u (a • k) = rayVelocity c n u k) := by sorry

end

end QAlgorithms.Papers.Independent.Renew46.P42
