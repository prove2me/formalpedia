-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P42_slowFlow_firstJet
-- name    : QAlgorithms.Papers.Independent.Renew46.P42.slowFlow_firstJet
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T21:22:03.58234+00:00
-- url     : https://prove2.me/theorems/f3cdb9b8-488b-487e-9b59-a34ec1b2c1fa
-- title:
--   First-order Hamiltonian and vector Fresnel drag
-- statement:
--   In the local nondispersive ray model let $c>0$, $n\ge1$, $\mathbf k\ne0$, and let $\mathbf u$ be any fixed flow direction. A relation $f\sim_1g$ means equal values and equal actual derivatives at $\epsilon=0$. Let $H_\epsilon$ be (34) evaluated at flow $\epsilon\mathbf u$, and let $\mathbf v_\epsilon=\partial_{\mathbf k}H_\epsilon$. Then
--
--   $$H_\epsilon\sim_1\frac{c|\mathbf k|}{n}+\epsilon(1-n^{-2})\mathbf u\cdot\mathbf k,\qquad \mathbf v_\epsilon\sim_1\frac cn\frac{\mathbf k}{|\mathbf k|}+\epsilon(1-n^{-2})\mathbf u.$$
--
--   For any real frequency $\omega$, the dispersion polynomial $D_\epsilon$ of (33) also satisfies
--
--   $$-D_\epsilon/c^2\sim_1|\mathbf k|^2-n^2\omega^2/c^2+2\omega(n^2-1)\epsilon\mathbf u\cdot\mathbf k/c^2.$$
--
--   This is the vector Fresnel law and the unambiguous first-order dispersion symbol. Every fixed direction is subluminal on some neighborhood of zero flow; no finite-flow approximation bound is asserted.
-- source:
--   Optics of Nonuniformly Moving Media, arXiv:physics/9906038v3, PDF p. 3, §II, (7)–(11): first-order Hamiltonian and vector Fresnel drag

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P42

namespace QAlgorithms.Papers.Independent.Renew46.P42

noncomputable section

open scoped BigOperators

open Filter Set MeasureTheory

-- Reuse the pinned accepted real quadratic form (arbitrary finite real matrices).

open QAlgorithms.Papers.Independent.Information100.P37 (quadratic)

/-- PDF p.3, (7)–(11), and p.5: first jets of the relativistic Hamiltonian,
Fresnel velocity, and rayDispersion symbol. These are not finite-flow equalities. -/
theorem slowFlow_firstJet (c n omega : ℝ) (u k : V3)
    (hc : 0 < c) (hn : 1 ≤ n) (hk : k ≠ 0) :
    FirstJetEq (fun eps => rayHamiltonian c n (eps • u) k)
      (fun eps => c * length3 k / n + eps * (1 - 1 / n ^ 2) * dot3 u k) ∧
    FirstJetEq (fun eps => rayVelocity c n (eps • u) k)
      (fun eps => (c / n) • ((1 / length3 k) • k) +
        (eps * (1 - 1 / n ^ 2)) • u) ∧
    FirstJetEq (fun eps => -rayDispersion c n (eps • u) k omega / c ^ 2)
      (fun eps => dot3 k k - n ^ 2 * omega ^ 2 / c ^ 2 +
        2 * omega * (n ^ 2 - 1) * eps * dot3 u k / c ^ 2) := by sorry

end

end QAlgorithms.Papers.Independent.Renew46.P42
