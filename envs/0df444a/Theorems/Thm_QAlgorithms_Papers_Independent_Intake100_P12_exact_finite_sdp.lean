-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P12_exact_finite_sdp
-- name    : QAlgorithms.Papers.Independent.Intake100.P12.exact_finite_sdp
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T12:59:54.329675+00:00
-- url     : https://prove2.me/theorems/311290d5-e842-427d-ba27-140413ae60c2
-- title:
--   Exact finite SDP and attained physical optimum
-- statement:
--   Let $d,k\ge1$, and choose the parallel, fixed-order adaptive, or general process class. Let $f$ be a complex-linear map on single-channel Choi matrices whose values on unitary channels are unitary-channel Choi matrices. There is a finite basis $\{C(U_i^{\otimes k})\}_i$ consisting of actual repeated-unitary inputs, and a finite affine normalization system $A(C)=b$ for the chosen physical class, such that its achievable constant coefficients are exactly
--
--   $$\left\{p\in[0,1]:\exists S,F\succeq0,\ A(S+F)=b,\ \mathcal L_S(C(U_i^{\otimes k}))=p f(C(U_i))\ \text{for every }i\right\}.$$
--
--   Here $\mathcal L$ is the source link contraction with full transpose on the contracted oracle factors. Every feasible pair has a physical realization in the chosen class with exactly $k$ oracle slots, and every such physical instrument gives a feasible pair. A maximizing pair exists. General-process normalization uses a finite basis of augmented Choi tensors of arbitrary independent channel tuples; the other two systems are the explicit parallel and sequential comb equations.
--
--   This is an exact optimization characterization, with no numerical precision or running-time assertion.
-- source:
--   Probabilistic exact universal quantum circuits for transforming unitary operations, arXiv:1909.01366v2, PDF p. 7, III, Eqs. (15)–(20)

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P12

noncomputable section

open QAlgorithms

open scoped Matrix ComplexConjugate ComplexOrder Kronecker

namespace QAlgorithms.Papers.Independent.Intake100.P12

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Dependency50.P26 (ChannelChoi)

/-- PDF pp.6–7, Eqs. (15)–(20): finite SDP with both directions of physical
class equivalence and an attained optimum. The finite normalization map is a
conclusion, not a hypothesis. For General this uses independent-channel
normalization and never the inconsistent printed Eq. (14). -/
theorem exact_finite_sdp {d k : ℕ} (hd : 0 < d) (hk : 0 < k)
    (c : ProtocolClass)
    (f : Op (Fin d × Fin d) →ₗ[ℂ] Op (Fin d × Fin d)) (hf : UnitaryLinearTarget f) :
    ∃ n : ℕ, ∃ B : Fin n → Matrix.unitaryGroup (Fin d) ℂ,
    ∃ v : ℕ, ∃ N : Fin v → ChannelFamily (uniformWires d k),
    ∃ r : ℕ, ∃ A : Op (ProcessBasis (uniformWires d k)) →ₗ[ℝ] (Fin r → ℝ),
    ∃ b : Fin r → ℝ,
      IsUnitaryBasis d k n B ∧ IsNormalizationBasis (uniformWires d k) v N ∧
      (∀ C, ClassRealizable c d k C ↔ FiniteClassNormalized c N C) ∧
      (∀ C, FiniteClassNormalized c N C ↔ C.PosSemidef ∧ A C = b) ∧
      (∀ p S F, TestedFeasible (k := k) c f B p S F ↔
        0 ≤ p ∧ p ≤ 1 ∧ S.PosSemidef ∧ F.PosSemidef ∧ A (S+F) = b ∧
          ∀ i, evaluateOracleSlots S (repeatedChoi k (B i)) = (p : ℂ) • f (gateChoi (B i : Op (Fin d)))) ∧
      (∀ p, Attainable c d k (fun U => f (gateChoi (U : Op (Fin d)))) p ↔
        ∃ S F, TestedFeasible (k := k) c f B p S F) ∧
      (∃ p : ℝ, ∃ S F : Op (ProcessBasis (uniformWires d k)),
        TestedFeasible (k := k) c f B p S F ∧
        ∀ q : ℝ, (∃ T G : Op (ProcessBasis (uniformWires d k)),
          TestedFeasible (k := k) c f B q T G) → q ≤ p) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P12

end
