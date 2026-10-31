-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P82_Gibbs_fluctuation_principle
-- name    : QAlgorithms.Papers.Independent.Intake100.P82.Gibbs_fluctuation_principle
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:21:30.983253+00:00
-- url     : https://prove2.me/theorems/4443880a-5921-487a-acc7-462338d2915e
-- title:
--   Theorem 4.7: Gibbs fluctuation principle
-- statement:
--   Let $M$ be a nonempty compact metric space with its Borel sigma-algebra, and let $\varphi:M\to M$ be continuous. Write $\mathcal P(M)$ for Borel probabilities with the weak topology, $\mathcal P_\varphi(M)$ for invariant probabilities, and $\mathcal E_\varphi(M)$ for ergodic probabilities. Entropy $h_\varphi$ is Kolmogorov–Sinai entropy with natural logarithms. For a bounded Borel sequence $\mathcal G=(G_n)_{n\ge1}$, asymptotic additivity means uniform approximation at linear scale by sums $S_n g=\sum_{j=0}^{n-1}g\circ\varphi^j$ of continuous functions. For such a sequence, $\mathcal G(Q)$ denotes the constructed real limit of $n^{-1}\int G_n\,dQ$ on invariant probabilities, and $p(\mathcal G)$ denotes its topological pressure. All time limits use positive integers.
--
--   Condition USCE means finite topological entropy and upper semicontinuity of $Q\mapsto h_\varphi(Q)$ on invariant probabilities. S is ordinary specification; WPS is the source weak periodic specification; PAP is finiteness of periodic sets and convergence of their normalized log partition sums to pressure.
--
--   Choose either C-Commutation, where $\theta$ is an involutive homeomorphism and $\varphi=\theta\circ\varphi\circ\theta$, or R-Reversal, where additionally $\varphi$ is a homeomorphism and $\varphi^{-1}=\theta\circ\varphi\circ\theta$. Set $\theta_n=\theta$ in C and $\theta_n=\theta\circ\varphi^{n-1}$ in R, $\widehat G_n=G_n\circ\theta_n$, $\sigma_n=G_n-\widehat G_n$, and $\operatorname{ep}(Q)=\mathcal G(Q)-\mathcal G(\theta_*Q)$ for invariant $Q$.
--
--   The empirical measure is $\mu_n^x=n^{-1}\sum_{j=0}^{n-1}\delta_{\varphi^j(x)}$. An LDP below is the full speed-$n$ Borel-set principle, with interior in the lower bound and closure in the upper bound. Put
--   $$J_{\mathcal G}(Q)=\begin{cases}p(\mathcal G)-\mathcal G(Q)-h_\varphi(Q),&Q\in\mathcal P_\varphi(M),\\+\infty,&\text{otherwise}.\end{cases}$$
--
--   Assume USCE and S and let $P$ be a weak Gibbs probability for $\mathcal G\in\mathcal A(M)$. Under the single fixed law $P$:
--
--   The empirical rate satisfies $J_{\mathcal G}(\theta_*Q)=J_{\mathcal G}(Q)+\operatorname{ep}(Q)$ for every invariant $Q$. Moreover $\sigma_n/n$ obeys the full LDP with good convex rate
--   $$I(s)=\inf_{\substack{Q\in\mathcal P_\varphi(M)\\\operatorname{ep}(Q)=s}}J_{\mathcal G}(Q),\qquad I(-s)=I(s)+s.$$
--   Writing $e(\alpha)=p((1-\alpha)\mathcal G+\alpha\widehat{\mathcal G})-p(\mathcal G)$, one also has $I(s)=\sup_\alpha\{\alpha s-e(-\alpha)\}$.
--
--   The law need not be invariant, ergodic, or equivalent to its reversal.
-- source:
--   Fluctuation Theorem and Thermodynamic Formalism, arXiv:1712.05167v3, PDF p. 32, Theorem 4.7: Gibbs fluctuation principle

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

/-- Theorem 4.7, arXiv:1712.05167v3, PDF p.32: empirical FR, scalar FT/FR,
goodness, convexity, and duality under a fixed weak Gibbs probability. -/
theorem Gibbs_fluctuation_principle (phi : M → M) (hphi : Continuous phi)
    (hu : USCE phi) (hs : Specification phi) (theta : M ≃ₜ M) (rev : Bool)
    (hsym : Symmetry phi theta rev) (G : ℕ → M → ℝ)
    (hG : AsymptoticallyAdditive phi G) (P : ProbabilityMeasure M)
    (hg : WeakGibbs phi G P) :
    FluctuationPrinciple phi G theta rev (fun _ => (P : Measure M)) := by sorry

end CompactDynamics

end QAlgorithms.Papers.Independent.Intake100.P82

end
