-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P82_cylinder_potentials
-- name    : QAlgorithms.Papers.Independent.Intake100.P82.cylinder_potentials
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:08:51.366699+00:00
-- url     : https://prove2.me/theorems/2f1ae1d2-bcdf-4c18-bbfe-85912bb31a53
-- title:
--   Example 0.16: cylinder potentials and quasi-Bernoulli measures
-- statement:
--   Let $M$ be a nonempty compact metric space with its Borel sigma-algebra, and let $\varphi:M\to M$ be continuous. Write $\mathcal P(M)$ for Borel probabilities with the weak topology, $\mathcal P_\varphi(M)$ for invariant probabilities, and $\mathcal E_\varphi(M)$ for ergodic probabilities. Entropy $h_\varphi$ is Kolmogorov–Sinai entropy with natural logarithms. For a bounded Borel sequence $\mathcal G=(G_n)_{n\ge1}$, asymptotic additivity means uniform approximation at linear scale by sums $S_n g=\sum_{j=0}^{n-1}g\circ\varphi^j$ of continuous functions. For such a sequence, $\mathcal G(Q)$ denotes the constructed real limit of $n^{-1}\int G_n\,dQ$ on invariant probabilities, and $p(\mathcal G)$ denotes its topological pressure. All time limits use positive integers.
--
--   Choose either C-Commutation, where $\theta$ is an involutive homeomorphism and $\varphi=\theta\circ\varphi\circ\theta$, or R-Reversal, where additionally $\varphi$ is a homeomorphism and $\varphi^{-1}=\theta\circ\varphi\circ\theta$. Set $\theta_n=\theta$ in C and $\theta_n=\theta\circ\varphi^{n-1}$ in R, $\widehat G_n=G_n\circ\theta_n$, $\sigma_n=G_n-\widehat G_n$, and $\operatorname{ep}(Q)=\mathcal G(Q)-\mathcal G(\theta_*Q)$ for invariant $Q$.
--
--   The empirical measure is $\mu_n^x=n^{-1}\sum_{j=0}^{n-1}\delta_{\varphi^j(x)}$. An LDP below is the full speed-$n$ Borel-set principle, with interior in the lower bound and closure in the upper bound. Put
--   $$J_{\mathcal G}(Q)=\begin{cases}p(\mathcal G)-\mathcal G(Q)-h_\varphi(Q),&Q\in\mathcal P_\varphi(M),\\+\infty,&\text{otherwise}.\end{cases}$$
--
--   Let $M$ be a primitive two-sided finite-type subshift, with left shift $\varphi$, and let $\theta(x)_j=p(x_{-j})$ for an involutive alphabet permutation preserving $M$. Let $P$ be a fully supported invariant probability. For positive $n$ put
--   $$G_n(x)=\log P\{y:y_j=x_j\text{ for }1\le j\le n\}.$$
--   Every $G_n$ is continuous. If $(G_n)$ is asymptotically additive, then its pressure is zero, $P$ is weak Gibbs for it, and the empirical/scalar LDP and fluctuation principle hold under $P$. In particular, if these cylinder log potentials satisfy both fixed-constant almost-additive inequalities (0.18) and (0.19), they are asymptotically additive and all these conclusions hold. This is the quasi-Bernoulli application; pressure zero is proved, not imposed.
-- source:
--   Fluctuation Theorem and Thermodynamic Formalism, arXiv:1712.05167v3, PDF p. 10, Example 0.16: cylinder potentials and quasi-Bernoulli measures

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P82

noncomputable section

open Filter MeasureTheory Set

open scoped Topology BigOperators ENNReal

namespace QAlgorithms.Papers.Independent.Intake100.P82

attribute [local instance] Classical.propDecidable

section CompactDynamics

variable {M : Type*} [instMetric : MetricSpace M] [instCompact : CompactSpace M]
  [instNonempty : Nonempty M] [instMeasurable : MeasurableSpace M] [instBorel : BorelSpace M]

-- Retain standing assumptions even when a displayed lemma does not use them.

include instCompact instNonempty instBorel

local instance : DecidableEq M := Classical.decEq M

/-- Example 0.16, arXiv:1712.05167v3, PDF p.10. Coordinates start at one;
pressure zero is a conclusion. Quasi-Bernoulli means both fixed-constant
inequalities (0.18)/(0.19), equivalently almost additivity of the cylinder logs. -/
theorem cylinder_potentials (phi : M → M) (hphi : Continuous phi)
    (S : ShiftPresentation phi) (theta : M ≃ₜ M) (htheta : ShiftReversal phi S theta)
    (P : ProbabilityMeasure M) (hP : ProbabilityInvariant phi P) (hsupport : OpenSetFullSupport P) :
    let G := cylinderPotential phi S P
    (∀ n : ℕ, 1 ≤ n → Continuous (G n)) ∧
    (AsymptoticallyAdditive phi G →
      separatedSetPressure phi G = 0 ∧ WeakGibbs phi G P ∧
      EmpiricalScalarLDP phi G (fun _ => (P : Measure M)) ∧
      FluctuationPrinciple phi G theta true (fun _ => (P : Measure M))) ∧
    (AlmostAdditive phi G → AsymptoticallyAdditive phi G ∧
      separatedSetPressure phi G = 0 ∧ WeakGibbs phi G P ∧
      EmpiricalScalarLDP phi G (fun _ => (P : Measure M)) ∧
      FluctuationPrinciple phi G theta true (fun _ => (P : Measure M))) := by sorry

end CompactDynamics

end QAlgorithms.Papers.Independent.Intake100.P82

end
