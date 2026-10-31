-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P64_quantum_conditionalHTheorem
-- name    : QAlgorithms.Papers.Independent.Intake100.P64.quantum_conditionalHTheorem
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:22:50.988752+00:00
-- url     : https://prove2.me/theorems/11de1bcf-cc19-4447-aa3b-153823dfb46d
-- title:
--   §4.2.2: conditional quantum H-theorem, (4.19)
-- statement:
--   Let $\mathcal H$ be a separable complete complex Hilbert space and let $(T_t)_{t\ge0}$ be a given trace-norm-continuous, completely positive, trace-preserving linear semigroup on its full trace class. Let $\rho,\sigma$ be normalized positive trace-class states with $T_t\sigma=\sigma$, and let $k_B>0$. For the accepted extended Umegaki relative entropy in nats, put $S(\rho\mid\sigma)=k_BD(\rho\Vert\sigma)$. Then
--   $$
--   t\longmapsto S(T_t\rho\mid\sigma)\text{ is nonincreasing},\qquad
--   \frac{d}{dt}S(T_t\rho\mid\sigma)\le0
--   $$
--   wherever $t>0$ and this entropy curve is locally finite and differentiable. This conditional implication applies to the source's given finite-volume trace-class realization; it does not assert existence of such a Boltzmann realization.
-- source:
--   Quantum linear Boltzmann equation, arXiv:0904.3911v3, PDF p. 17, §4.2.2: conditional quantum H-theorem, (4.19)

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P64

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal NNReal Topology

namespace QAlgorithms.Papers.Independent.Intake100.P64

local notation "TransversePlane" => QAlgorithms.Papers.Independent.Renew46.P04.Plane ℝ

-- The accepted rising factorial has exactly the same finite-product body.

open QAlgorithms.Papers.Independent.Claimed50.P39 (rising)

open QAlgorithms.Papers.Independent.Dependency50.P13
  (TraceClass State relativeEntropy traceNormTopology)

open QAlgorithms.Papers.Independent.Next46.P09 (IsTraceLinear IsTraceCP)

/-- PDF p.17, (4.19): conditional H-theorem for a given conservative QDS
and invariant trace-class state. Local finiteness prevents the toReal default
at infinity from becoming a spurious differentiable entropy curve. -/
theorem quantum_conditionalHTheorem {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    {I : Type*} (b : HilbertBasis I ℂ H) (T : ConservativeQDS b)
    (rho sigma : State b) (hinvariant : ∀ t, T.stateMap t sigma = sigma)
    (kB : ℝ) (hkB : 0 < kB) :
    Antitone (fun t : NNReal => boltzmannRelativeEntropy kB (T.stateMap t rho) sigma) ∧
    (∀ t : ℝ, 0 < t →
      (∃ epsilon : ℝ, 0 < epsilon ∧ ∀ s : ℝ, |s - t| < epsilon →
        boltzmannRelativeEntropy kB (T.stateMap s.toNNReal rho) sigma ≠ ⊤) →
      DifferentiableAt ℝ
        (fun s : ℝ => (boltzmannRelativeEntropy kB (T.stateMap s.toNNReal rho) sigma).toReal) t →
      deriv (fun s : ℝ =>
        (boltzmannRelativeEntropy kB (T.stateMap s.toNNReal rho) sigma).toReal) t ≤ 0) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P64

end
