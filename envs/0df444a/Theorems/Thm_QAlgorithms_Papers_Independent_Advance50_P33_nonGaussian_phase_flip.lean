-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P33_nonGaussian_phase_flip
-- name    : QAlgorithms.Papers.Independent.Advance50.P33.nonGaussian_phase_flip
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T13:31:19.252523+00:00
-- url     : https://prove2.me/theorems/db40139b-7f93-49f7-85ea-7073d2c4d660
-- title:
--   A proof-only non-Gaussian bit flip in the large-amplitude norm limit
-- statement:
--   Let $D(a)$ be the oscillator Weyl displacement and $Q_0=|0\rangle\langle0|$ the vacuum projector. Define the unitary
--   $$
--   U_{\rm NG}(a)=D(-a)(I-2Q_0)D(a).
--   $$
--   For $a>0$ real, let $|\chi_b(a)\rangle$ be the normalized token--proof encoding of Eq. (3), with $b\in\{0,1\}$. Alice acts only on the proof, leaving Bob's token unchanged. For each bit,
--   $$
--   \lim_{a\to+\infty}\left\|(I\otimes U_{\rm NG}(a))|\chi_b(a)\rangle+|\chi_{1-b}(a)\rangle\right\|_2=0.
--   $$
--   The plus sign fixes the global minus phase of the output. This gives a possible asymptotic attack; it is not an exact finite-amplitude phase flip or an optimality assertion. The bounded reflection $I-2Q_0$ realizes the exponential in Eq. (6).
-- source:
--   Quantum bit commitment under Gaussian constraints, arXiv:1105.2140v2, PDF p. 3, III.A, Eq.(6): asymptotic non-Gaussian local bit flip

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P33

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P33

open Filter

open scoped BigOperators Topology

open QAlgorithms.Papers.Independent.Dependency50.P39
  (Fock FockOperator BipartiteFock fockKet bipartiteKet coherentKet
   coherentCoefficient CoherentRealized displacement displacementMatrix
   DisplacementRealized HasFockMatrix operatorOfMatrix IsDensity IsTraceClass
   nuclearTraceNorm fockTrace)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.3--4, Eq.(6): a possible non-Gaussian proof-only bit flip in the
large-positive-real-amplitude norm limit. The overall minus sign is immaterial
physically, but retained here for exact vector convergence. No finite-a exact
phase flip and no assertion of optimality is made. -/
theorem nonGaussian_phase_flip :
    CoherentRealized ∧ DisplacementRealized ∧
    (∀ a : ℂ, (nonGaussianFlip a).adjoint.comp (nonGaussianFlip a) = 1 ∧
      (nonGaussianFlip a).comp (nonGaussianFlip a).adjoint = 1) ∧
    ∀ b : Bool, Tendsto
      (fun a : ℝ => ‖attackedChi (a : ℂ) b (nonGaussianFlip (a : ℂ)) + commitmentEncoding (a : ℂ) (!b)‖)
      atTop (nhds 0) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P33

end
