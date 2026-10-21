-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P42_magneticRay_firstJet
-- name    : QAlgorithms.Papers.Independent.Renew46.P42.magneticRay_firstJet
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T21:22:48.5308+00:00
-- url     : https://prove2.me/theorems/a3eaa08b-ca99-4af1-bb4b-4dac307e3666
-- title:
--   Lorentz-type ray force and canonical momentum shift
-- statement:
--   Let $c>0$, $n\ge1$ be constant and let $\mathbf u$ be a stationary $C^2$ flow on an open spatial patch containing $\mathbf x$. Fix $\mathbf k\ne0$. Set $\mathbf u_\epsilon=\epsilon\mathbf u$, $H_\epsilon=H(\mathbf x,\mathbf k;\mathbf u_\epsilon)$, $\mathbf w_\epsilon=|\mathbf k|\partial_{\mathbf k}H_\epsilon$, and $X_\epsilon=(\partial_{\mathbf k}H_\epsilon,-\partial_{\mathbf x}H_\epsilon)$. Equality $\sim_1$ means equality of values and first derivatives at zero flow. Then
--
--   $$\mathbf w_\epsilon\sim_1\frac cn\left(\mathbf k+\frac{n^2-1}{c^2}H_\epsilon\mathbf u_\epsilon\right),\qquad X_\epsilon\mathbf w_\epsilon\sim_1(1-n^{-2})(\nabla\times\mathbf u_\epsilon)\times\mathbf w_\epsilon.$$
--
--   Moreover $X_\epsilon|\mathbf w_\epsilon|^2\sim_10$, $X_\epsilon H_\epsilon\sim_10$, $|\mathbf w_\epsilon|^2\sim_1H_\epsilon^2$, and
--
--   $$\mathbf k\sim_1\frac nc\mathbf w_\epsilon-\frac{n^2-1}{c^2}H_\epsilon\mathbf u_\epsilon.$$
--
--   The force and conservation laws are computed from Hamilton's vector field, giving the magnetic analogy at precisely the retained order.
-- source:
--   Optics of Nonuniformly Moving Media, arXiv:physics/9906038v3, PDF p. 3, §II, (12)–(16),(18): Lorentz-type ray force and momentum shift

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P42

namespace QAlgorithms.Papers.Independent.Renew46.P42

noncomputable section

open scoped BigOperators

open Filter Set MeasureTheory

-- Reuse the pinned accepted real quadratic form (arbitrary finite real matrices).

open QAlgorithms.Papers.Independent.Information100.P37 (quadratic)

/-- PDF p.3, (12)–(16),(18): stationary uniform-index magnetic ray model.
The force and conservation laws are conclusions about Hamiltonian derivatives. -/
theorem magneticRay_firstJet (c n : ℝ) (u : V3 → V3) (x k : V3) (O : Set V3)
    (hc : 0 < c) (hn : 1 ≤ n) (hk : k ≠ 0)
    (hO : IsOpen O) (hx : x ∈ O) (hreg : ContDiffOn ℝ 2 u O) :
    FirstJetEq (fun eps => modifiedVelocity c n (eps • u x) k)
      (fun eps => (c / n) • (k +
        ((n ^ 2 - 1) * rayHamiltonian c n (eps • u x) k / c ^ 2) • (eps • u x))) ∧
    FirstJetEq (fun eps => alongField c n eps u
        (fun z => modifiedVelocity c n (eps • u z.1) z.2) (x, k))
      (fun eps => (1 - 1 / n ^ 2) •
        cross3 (eps • curl3 u x) (modifiedVelocity c n (eps • u x) k)) ∧
    FirstJetEq (fun eps => alongField c n eps u
        (fun z => dot3 (modifiedVelocity c n (eps • u z.1) z.2)
          (modifiedVelocity c n (eps • u z.1) z.2)) (x, k)) (fun _ => (0 : ℝ)) ∧
    FirstJetEq (fun eps => alongField c n eps u
        (fun z => rayHamiltonian c n (eps • u z.1) z.2) (x, k)) (fun _ => (0 : ℝ)) ∧
    FirstJetEq (fun eps => dot3 (modifiedVelocity c n (eps • u x) k)
        (modifiedVelocity c n (eps • u x) k))
      (fun eps => (rayHamiltonian c n (eps • u x) k) ^ 2) ∧
    FirstJetEq (fun _ => k)
      (fun eps => (n / c) • modifiedVelocity c n (eps • u x) k -
        ((n ^ 2 - 1) * rayHamiltonian c n (eps • u x) k / c ^ 2) • (eps • u x)) := by sorry

end

end QAlgorithms.Papers.Independent.Renew46.P42
