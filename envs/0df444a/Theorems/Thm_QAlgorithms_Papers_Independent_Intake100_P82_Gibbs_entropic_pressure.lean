-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P82_Gibbs_entropic_pressure
-- name    : QAlgorithms.Papers.Independent.Intake100.P82.Gibbs_entropic_pressure
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:21:02.53171+00:00
-- url     : https://prove2.me/theorems/8202d3e0-33a3-4e26-bae8-d49c3ad3c0c6
-- title:
--   Unnumbered main identity: Gibbs entropic pressure
-- statement:
--   Let $M$ be a nonempty compact metric space with its Borel sigma-algebra, and let $\varphi:M\to M$ be continuous. Write $\mathcal P(M)$ for Borel probabilities with the weak topology, $\mathcal P_\varphi(M)$ for invariant probabilities, and $\mathcal E_\varphi(M)$ for ergodic probabilities. Entropy $h_\varphi$ is Kolmogorov–Sinai entropy with natural logarithms. For a bounded Borel sequence $\mathcal G=(G_n)_{n\ge1}$, asymptotic additivity means uniform approximation at linear scale by sums $S_n g=\sum_{j=0}^{n-1}g\circ\varphi^j$ of continuous functions. For such a sequence, $\mathcal G(Q)$ denotes the constructed real limit of $n^{-1}\int G_n\,dQ$ on invariant probabilities, and $p(\mathcal G)$ denotes its topological pressure. All time limits use positive integers.
--
--   Condition USCE means finite topological entropy and upper semicontinuity of $Q\mapsto h_\varphi(Q)$ on invariant probabilities. S is ordinary specification; WPS is the source weak periodic specification; PAP is finiteness of periodic sets and convergence of their normalized log partition sums to pressure.
--
--   Choose either C-Commutation, where $\theta$ is an involutive homeomorphism and $\varphi=\theta\circ\varphi\circ\theta$, or R-Reversal, where additionally $\varphi$ is a homeomorphism and $\varphi^{-1}=\theta\circ\varphi\circ\theta$. Set $\theta_n=\theta$ in C and $\theta_n=\theta\circ\varphi^{n-1}$ in R, $\widehat G_n=G_n\circ\theta_n$, $\sigma_n=G_n-\widehat G_n$, and $\operatorname{ep}(Q)=\mathcal G(Q)-\mathcal G(\theta_*Q)$ for invariant $Q$.
--
--   Retain the surrounding USCE and S assumptions and let $P$ be a weak Gibbs probability for $\mathcal G\in\mathcal A(M)$. For every real $\alpha$, the following finite limit exists:
--   $$\lim_{n\to\infty}\frac1n\log\int e^{-\alpha\sigma_n}\,dP=p((1-\alpha)\mathcal G+\alpha\widehat{\mathcal G})-p(\mathcal G).$$
--   The law is the single fixed $P$, which need not be invariant or equivalent to its reversal. This computes asymptotic entropic pressure and does not assert a finite-time RN identity for $P$.
-- source:
--   Fluctuation Theorem and Thermodynamic Formalism, arXiv:1712.05167v3, PDF p. 32, Unnumbered main identity: Gibbs entropic pressure

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

/-- Gibbs entropic-pressure identity, arXiv:1712.05167v3, PDF p.32.
No equivalence of P with its reversal and no finite-time RN identity is assumed. -/
theorem Gibbs_entropic_pressure (phi : M → M) (hphi : Continuous phi)
    (hu : USCE phi) (hs : Specification phi) (theta : M ≃ₜ M) (rev : Bool)
    (hsym : Symmetry phi theta rev) (G : ℕ → M → ℝ)
    (hG : AsymptoticallyAdditive phi G) (P : ProbabilityMeasure M)
    (hg : WeakGibbs phi G P) (a : ℝ) :
    ∃ e : ℝ, entropicPressure phi G theta rev a = (e : EReal) ∧
      Tendsto (fun n : ℕ => logSpeed (n + 1) (∫⁻ x,
        ENNReal.ofReal (Real.exp (-a * sequenceEntropyProduction phi theta rev G (n + 1) x))
          ∂(P : Measure M))) atTop (𝓝 (e : EReal)) := by sorry

end CompactDynamics

end QAlgorithms.Papers.Independent.Intake100.P82

end
