-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P45_covariant_generator_coefficient
-- name    : QAlgorithms.Papers.Independent.Renew46.P45.covariant_generator_coefficient
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T21:42:59.267031+00:00
-- url     : https://prove2.me/theorems/af296dbd-23f1-4dfb-a9c1-53e556932ce9
-- title:
--   One scalar on all traceless infinitesimal generators
-- statement:
--   Let $d\ge2$, $N\ge1$, and let $\pi:U(d)\to U(H_\pi)$ be an actual smooth unitary representation on any finite-dimensional complex Hilbert space. Let $K=\operatorname{Sym}^N\mathbb C^d$ and let $\pi_N^+$ be its actual tensor representation. Suppose $T:B(H_\pi)\to B(K)$ is complex-linear, completely positive, unital, and covariant:
--   $$
--   T(\pi(u)A\pi(u)^*)=\pi_N^+(u)T(A)\pi_N^+(u)^*.
--   $$
--   There is a single number $c\in\mathbb C$ such that
--   $$
--   T(\partial\pi(a))=c\left.\sum_{k=1}^N a_{(k)}\right|_K\qquad(a\in B(\mathbb C^d),\ \operatorname{tr}a=0).
--   $$
--   Here $\partial\pi$ is the actual infinitesimal representation, extended complex linearly from the anti-Hermitian matrices; $a$ need not be anti-Hermitian. The conclusion reduces the entire traceless generator action to one coefficient.
-- source:
--   Optimal Cloning of Pure States, Judging Single Clones, arXiv:quant-ph/9807010v1, PDF p. 5, Corollary 4

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P45

noncomputable section

open scoped Matrix ComplexOrder

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Renew46.P45

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P26 (Mat)

open QAlgorithms.Papers.Independent.Information100.P58 (Word)

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P45.unitaryMeasurable

/-- PDF p.5 Corollary 4, complexification p.12: ANY finite-dimensional
smooth unitary domain representation; traceless a need not be anti-Hermitian. -/
theorem covariant_generator_coefficient (d N h : ℕ) (hd : 2 ≤ d) (hN : 1 ≤ N)
    (pi : SmoothUnitaryRep d h) (T : Mat h → TensorMat d N)
    (hCP : IsBoseCP d N T) (hunital : T 1 = boseProjector d N)
    (hcov : ∀ u : U d, ∀ A : Mat h,
      T ((pi.action u : Mat h) * A * (pi.action u : Mat h)ᴴ) =
        QAlgorithms.piKron N (u : Mat d) * T A * (QAlgorithms.piKron N (u : Mat d))ᴴ) :
    ∃ c : ℂ, ∀ a : Mat d, Matrix.trace a = 0 →
      T (pi.differential a) = c • boseGenerator d N a := by sorry

end QAlgorithms.Papers.Independent.Renew46.P45

end
