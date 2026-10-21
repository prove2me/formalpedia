-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P36_qubitDephasingBoundary
-- name    : QAlgorithms.Papers.Independent.Renew46.P36.qubitDephasingBoundary
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T22:14:48.81998+00:00
-- url     : https://prove2.me/theorems/b7650fb4-1622-47fe-b0b7-6127d414c653
-- title:
--   Appendix B: binary ensemble qubit trade-off
-- statement:
--   Fix $p\in[0,1]$ and the qubit channel $\mathcal N_p=(1-p)\mathrm{id}_2+p\Delta_2$, where $\Delta_2$ is complete dephasing. Let $h_2(t)=-t\log_2t-(1-t)\log_2(1-t)$, with $0\log_20=0$. For $0\leq\mu\leq\tfrac12$ set
--
--   $$
--   a_p(\mu)=1-h_2(\mu),\qquad
--   b_p(\mu)=h_2(\mu)-h_2\!\left(\frac{1+\sqrt{1-4p(2-p)\mu(1-\mu)}}2\right).
--   $$
--
--   For each unassisted operational scenario $s\in\{\mathrm{Ia},\mathrm{Ib},\mathrm{II}\}$, the complete downward simultaneous region is
--
--   $$
--   S_s(\mathcal N_p)=\{(r,R)\geq0:\exists\mu\in[0,\tfrac12],\ r\leq a_p(\mu),\ R\leq b_p(\mu)\}.
--   $$
--
--   For every such $\mu$ there is a two-letter pure input–reference ensemble with equal probabilities and input marginals $\operatorname{diag}(\mu,1-\mu)$ and $\operatorname{diag}(1-\mu,\mu)$. Its classical mutual information and conditional coherent information equal $a_p(\mu)$ and $b_p(\mu)$, respectively. Entropies are in bits, and references and preparations are normalized.
--
--   This gives both the region and its attaining binary ensembles. At $p=1$ the quantum rate is zero; the statement does not assert Pareto maximality of every parametrized corner at this degeneracy.
--
--   **Formalization Note** Page 15 prints $16p(1-p)$, the phase-flip parameterization. The explicit channel on page 14 and Figure 2 instead use complete-dephasing weight $p$, whose phase-flip probability is $p/2$. Substitution yields $4p(2-p)$; the correction requires independent moderation.
-- source:
--   The capacity of a quantum channel for simultaneous transmission of classical and quantum information, arXiv:quant-ph/0311131v3, PDF p. 15, Appendix B: binary ensemble qubit trade-off

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P36

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Renew46.P36

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P08 (Ensemble canonicalPurification)

open QAlgorithms.Papers.Independent.Dependency50.P07 (Typical)

open QAlgorithms.Papers.Independent.Information100.P27 (qubitDephasing)

open QAlgorithms.Papers.Independent.Dependency50.P41 (maximallyEntangled)

open QAlgorithms.Papers.Independent.Claimed50.P20 (DynamicPureEnsemble pureOutputs cqHolevoBits conditionalCoherent)

open QAlgorithms.Papers.Independent.Information100.P67
  (IsDegradable receiverChannel complementaryChannel maximumCoherentInformation squaredFidelity)

open QAlgorithms.Papers.Independent.Information100.P76 (maximallyMixed)

open QAlgorithms.Papers.Independent.Information100.P80 (quantumCapacity)

open QAlgorithms.Papers.Independent.Next46.P40
  (dephasingIsometry generalizedDephasing diagonalPart)

variable {A B E A1 A2 E1 E2 : Type}

variable [Fintype A] [Fintype B] [Fintype E]

variable [Fintype A1] [Fintype A2] [Fintype E1] [Fintype E2]

/-- Appendix B, PDF pp.14--15 and Fig.2, p.5: downward binary-ensemble region
and the ensemble attaining each stated corner. The printed discriminant
16*p*(1-p) uses a phase-flip parameter; for the explicit channel (1-p)id+p*Delta
it must be 4*p*(2-p). At p=1 quantum rate is zero. No claim that all corners
are Pareto maximal is made at that degeneracy. Requires independent moderation. -/
theorem qubitDephasingBoundary
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (s : Scenario) :
    simultaneousOperationalRegion s (qubitDephasing (1 - p)) =
      {v : ℝ × ℝ | 0 ≤ v.1 ∧ 0 ≤ v.2 ∧ ∃ mu : ℝ, 0 ≤ mu ∧ mu ≤ 1 / 2 ∧
        v.1 ≤ (qubitCorner p mu).1 ∧ v.2 ≤ (qubitCorner p mu).2} ∧
    ∀ mu : ℝ, 0 ≤ mu → mu ≤ 1 / 2 → ∃ P : DynamicPureEnsemble (Fin 2),
      P.ensemble.size = 2 ∧ (∀ x, P.ensemble.prob x = 1 / 2) ∧
      (∀ x, ensembleInput P x = Matrix.diagonal (fun i : Fin 2 =>
        ((if i.val = 0 then (if x.val = 0 then mu else 1 - mu)
          else (if x.val = 0 then 1 - mu else mu)) : ℂ))) ∧
      classicalInformation (qubitDephasing (1 - p)) P = (qubitCorner p mu).1 ∧
      conditionalCoherentInformation (qubitDephasing (1 - p)) P = (qubitCorner p mu).2 := by sorry

end QAlgorithms.Papers.Independent.Renew46.P36

end
