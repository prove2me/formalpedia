-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P33_bayesianPackets_update
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P33.bayesianPackets_update
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:08:10.103121+00:00
-- url     : https://prove2.me/theorems/f6722739-ceda-4959-947b-78187376e1c5
-- title:
--   Local packet measurements update the residual common-phase law by Bayes rule
-- statement:
--   Let $a\ge0$, and start with $\rho_{K+M}(a)$. On each of the first $K$ packets perform a finite-outcome local quantum measurement, specified by bounded Kraus operators $A_{i,d,r}$ with a countable internal index $r$ and strong completeness $\sum_{d,r}A_{i,d,r}^{\dagger}A_{i,d,r}=I$. Fix an observed outcome string $D=(d_i)_{i<K}$. Construct its effects $E_{i,d_i}=\sum_r A_{i,d_i,r}^{\dagger}A_{i,d_i,r}$ from their convergent occupation sums. Write $P_\theta=|ae^{i\theta}\rangle\langle ae^{i\theta}|$ and define the actual Born likelihood and evidence by
--
--   $$
--   L_D(\theta)=\prod_{i<K}\operatorname{tr}(E_{i,d_i}P_\theta),\qquad
--   Z=\int_0^{2\pi}L_D(\theta)\frac{d\theta}{2\pi}.
--   $$
--
--   Assume $Z>0$. Apply the tensor Kraus instrument to the first $K$ packets, leaving $M$ packets untouched, sum its internal branches in trace norm, and trace out the measured packets. This constructs an unnormalized residual $R_D$; the actual outcome probability is $Z$, and
--
--   $$
--   R_D=\int_0^{2\pi}L_D(\theta)P_\theta^{\otimes M}\frac{d\theta}{2\pi},\qquad
--   \frac{R_D}{Z}=\int P_\theta^{\otimes M}\,d\lambda_D(\theta),
--   \quad d\lambda_D=\frac{L_D}{Z}\frac{d\theta}{2\pi}.
--   $$
--
--   All integral, Kraus-sum, effect and partial-trace constructions are genuine trace-class or bounded-operator realizations. The posterior law has mass one and $R_D/Z$ is a normalized density. Each effect's Born weight equals its convergent sum of Kraus output norm squares. The residual consequently depends only on effects, regardless of their local Kraus realization.
--
--   This is finite-data quantum conditioning, with no exact finite-data phase identification or purity conclusion. The empty measurement string has likelihood one; $M=0$ means a scalar residual.
-- source:
--   The Quantum State of a Propagating Laser Field, arXiv:quant-ph/0111157v1, PDF p. 5, IID, Eqs.(22)–(23)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P33

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P33

open Filter MeasureTheory

open scoped Topology Matrix ComplexConjugate

attribute [local instance] Classical.propDecidable

open QAlgorithms.Papers.Independent.Dependency50.P39

-- Accepted scalar phase; positive exponential, differing only by commuting scalars.

open QAlgorithms.Papers.Independent.Information100.P75 (phase)

/-- arXiv:quant-ph/0111157v1, PDF p.5, Eqs.(22)–(23).
Actual local quantum instruments on the first K packets give the computed
likelihood, evidence and posterior on M untouched packets. Arbitrary countable
internal Kraus realizations are allowed; after tracing the measured packets,
the answer depends only on the selected effects. Evidence must be positive.
K=0 and M=0 respectively mean no data and the scalar residual density. -/
theorem bayesianPackets_update {K M O : ℕ} (a : ℝ) (ha : 0 ≤ a)
    (A : Fin K → FockLocalInstrument O) (d : Fin K → Fin O)
    (hZ : 0 < packetEvidence A d a) :
    (∀ i : Fin K,
      HasFockMatrix (localEffect (A i) (d i)) (fun m n => ∑' k : ℕ × ℕ,
        star ((A i).kraus (d i) k.1 (fockKet m) k.2) *
          (A i).kraus (d i) k.1 (fockKet n) k.2) ∧
      (∀ theta, Summable (fun r : ℕ =>
        ‖(A i).kraus (d i) r (coherentKet ((a : ℂ) * phase theta))‖ ^ 2) ∧
        (inner (𝕜 := ℂ) (coherentKet ((a : ℂ) * phase theta))
          (localEffect (A i) (d i) (coherentKet ((a : ℂ) * phase theta)))).re =
        ∑' r : ℕ, ‖(A i).kraus (d i) r (coherentKet ((a : ℂ) * phase theta))‖ ^ 2)) ∧
    (∀ r, HasPacketMatrix (eventKraus M A d r) (fun m n =>
      if (m ∘ Fin.natAdd K) = (n ∘ Fin.natAdd K) then
        ∏ i : Fin K, (A i).kraus (d i) (r i)
          (fockKet (n (Fin.castAdd M i))) (m (Fin.castAdd M i)) else 0)) ∧
    TraceHasSum (eventTerm M A d a) (eventOutput M A d a) ∧
    (Summable (fun q => eventOutput M A d a (packetBasis q) q) ∧
      (∑' q, eventOutput M A d a (packetBasis q) q).re = packetEvidence A d a) ∧
    (∀ m n, Summable (fun q : Fin K → ℕ =>
      eventOutput M A d a (packetBasis (Fin.append q n)) (Fin.append q m))) ∧
    HasPacketMatrix (packetResidual M A d a) (fun m n => ∑' q : Fin K → ℕ,
      eventOutput M A d a (packetBasis (Fin.append q n)) (Fin.append q m)) ∧
    TraceIntegral phaseLaw (fun theta => (packetLikelihood A d a theta : ℂ) •
      packetProjector (fun _ : Fin M => (a : ℂ) * phase theta))
      (packetResidual M A d a) ∧
    IsProbabilityMeasure (posteriorPhaseLaw A d a) ∧
    IsPacketDensity (((packetEvidence A d a)⁻¹ : ℂ) • packetResidual M A d a) ∧
    TraceIntegral (posteriorPhaseLaw A d a)
      (fun theta => packetProjector (fun _ : Fin M => (a : ℂ) * phase theta))
      (((packetEvidence A d a)⁻¹ : ℂ) • packetResidual M A d a) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P33

end
