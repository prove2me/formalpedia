-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P11_hiddenOrthogonality
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P11.hiddenOrthogonality
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T04:50:11.869199+00:00
-- url     : https://prove2.me/theorems/cc553e17-3cee-445d-bb72-91c2f72111dd
-- title:
--   Hidden orthogonality permits a smaller sum rate
-- statement:
--   For $0<\alpha,\beta<1$, take three equiprobable product letters $|\phi_i\rangle_A|\psi_i\rangle_B$ in $\mathbb C^2\otimes\mathbb C^3$, where
--
--   $$
--   \begin{aligned}
--   \phi_1&=|0\rangle,&\phi_2&=\sqrt\alpha|0\rangle+\sqrt{1-\alpha}|1\rangle,&\phi_3&=|1\rangle,\\
--   \psi_1&=\sqrt{1-\beta}|0\rangle+\sqrt\beta|1\rangle,&\psi_2&=|1\rangle,&
--   \psi_3&=\sqrt{1-\beta}|2\rangle+\sqrt\beta|0\rangle.
--   \end{aligned}
--   $$
--
--   Let $\mathcal E_{AB}$ be this source and $\mathcal E_A,\mathcal E_B$ its marginals. Set $\psi'_1=\psi_1$, $\psi'_2=\psi_2$, $\psi'_3=|0\rangle$, and let $\mathcal E'_B$ be the corresponding equiprobable ensemble. Define the exact rates $r_A(\alpha)=S(\mathcal E_A)$, $r_B(\beta)=S(\mathcal E'_B)$ and the comparison expression $L(\alpha,\beta)=[S(\mathcal E_A)+S(\mathcal E_B)+S(\mathcal E_{AB})]/2$. Both local ensembles are irreducible, the joint ensemble is reducible, and $(r_A(\alpha),r_B(\beta))$ is achievable. Moreover, with $h=H_2(2/3)$ denoting binary entropy in bits,
--
--   $$
--   \begin{aligned}
--   (r_A(\alpha),r_B(\beta))&\longrightarrow(h,h),\\
--   r_A(\alpha)+r_B(\beta)&\longrightarrow 2h,\\
--   L(\alpha,\beta)&\longrightarrow h/2+\log_23
--   \end{aligned}
--   \qquad\text{as }(\alpha,\beta)\to(0,0)\text{ through positive values}.
--   $$
--
--   There is $\eta\in(0,1)$ such that $0<\alpha,\beta<\eta$ implies $r_A(\alpha)+r_B(\beta)<L(\alpha,\beta)$.
--
--   An achievable pair uses independent blind local CPTP encoders, one noiseless quantum link from each sender, and a joint CPTP decoder, without supplied shared entanglement or side messages. For every $\delta,\epsilon>0$, every sufficiently large positive integer blocklength $n$ admits positive compressed dimensions $d_A,d_B$ with $\log_2(d_A)/n\le R_A+\delta$, $\log_2(d_B)/n\le R_B+\delta$, and ensemble-average pure-input overlap with the reconstructed density operator at least $1-\epsilon$. Draws are independent and identically distributed; this is squared fidelity, without a purifying reference.
--
--   The example shows why the converse needs global irreducibility. Its approximate numbers describe limits, not exact finite-parameter rates.
-- source:
--   On the distributed compression of quantum information, arXiv:quant-ph/0403042v3, PDF p. 11, Section V.A: hidden orthogonality beats the global-irreducibility bound

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P11

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P11

open MeasureTheory Filter

open scoped BigOperators ComplexConjugate Matrix

open QAlgorithms.Papers.Independent.Dependency50.P19 (both)

open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.11, Section V.A, (23)–(30): local irreducibility does not imply the
rate-sum converse. Approximation is stated as positive-parameter limits and a
uniform sufficiently-small threshold, never as equality at positive parameters. -/
theorem hiddenOrthogonality :
    (∀ alpha beta : ℝ, 0 < alpha → alpha < 1 → 0 < beta → beta < 1 →
      EnsembleIrreducible (fun _ : Fin 3 => (1 / 3 : ℝ)) (hiddenAlice alpha) ∧
      EnsembleIrreducible (fun _ : Fin 3 => (1 / 3 : ℝ)) (hiddenBob beta) ∧
      ¬ EnsembleIrreducible (fun _ : Fin 3 => (1 / 3 : ℝ)) (hiddenJoint alpha beta) ∧
      FiniteAchievable (fun _ : Fin 3 => (1 / 3 : ℝ)) (hiddenJoint alpha beta)
        (hiddenRateA alpha) (hiddenRateB beta)) ∧
    Tendsto (fun x : ℝ × ℝ => (hiddenRateA x.1, hiddenRateB x.2))
      (nhdsWithin (0, 0) (Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ)))
      (nhds (binEntropy2 (2 / 3), binEntropy2 (2 / 3))) ∧
    Tendsto (fun x : ℝ × ℝ => hiddenRateA x.1 + hiddenRateB x.2)
      (nhdsWithin (0, 0) (Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ)))
      (nhds (2 * binEntropy2 (2 / 3))) ∧
    Tendsto (fun x : ℝ × ℝ => hiddenComparison x.1 x.2)
      (nhdsWithin (0, 0) (Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ)))
      (nhds (binEntropy2 (2 / 3) / 2 + Real.logb 2 3)) ∧
    ∃ eta : ℝ, 0 < eta ∧ eta < 1 ∧ ∀ alpha beta : ℝ,
      0 < alpha → alpha < eta → 0 < beta → beta < eta →
      hiddenRateA alpha + hiddenRateB beta < hiddenComparison alpha beta := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P11

end
