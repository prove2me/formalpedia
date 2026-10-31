-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P82_transformed_approximation
-- name    : QAlgorithms.Papers.Independent.Intake100.P82.transformed_approximation
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:16:34.645987+00:00
-- url     : https://prove2.me/theorems/b86c3806-9f01-4708-8e03-47eea7d69552
-- title:
--   Lemma 3.6: transformation of asymptotically additive potentials
-- statement:
--   Let $M$ be a nonempty compact metric space with its Borel sigma-algebra, and let $\varphi:M\to M$ be continuous. Write $\mathcal P(M)$ for Borel probabilities with the weak topology, $\mathcal P_\varphi(M)$ for invariant probabilities, and $\mathcal E_\varphi(M)$ for ergodic probabilities. Entropy $h_\varphi$ is Kolmogorov–Sinai entropy with natural logarithms. For a bounded Borel sequence $\mathcal G=(G_n)_{n\ge1}$, asymptotic additivity means uniform approximation at linear scale by sums $S_n g=\sum_{j=0}^{n-1}g\circ\varphi^j$ of continuous functions. For such a sequence, $\mathcal G(Q)$ denotes the constructed real limit of $n^{-1}\int G_n\,dQ$ on invariant probabilities, and $p(\mathcal G)$ denotes its topological pressure. All time limits use positive integers.
--
--   Condition USCE means finite topological entropy and upper semicontinuity of $Q\mapsto h_\varphi(Q)$ on invariant probabilities. S is ordinary specification; WPS is the source weak periodic specification; PAP is finiteness of periodic sets and convergence of their normalized log partition sums to pressure.
--
--   Choose either C-Commutation, where $\theta$ is an involutive homeomorphism and $\varphi=\theta\circ\varphi\circ\theta$, or R-Reversal, where additionally $\varphi$ is a homeomorphism and $\varphi^{-1}=\theta\circ\varphi\circ\theta$. Set $\theta_n=\theta$ in C and $\theta_n=\theta\circ\varphi^{n-1}$ in R, $\widehat G_n=G_n\circ\theta_n$, $\sigma_n=G_n-\widehat G_n$, and $\operatorname{ep}(Q)=\mathcal G(Q)-\mathcal G(\theta_*Q)$ for invariant $Q$.
--
--   Retain USCE, WPS, S and PAP. If $\mathcal G\in\mathcal A(M)$ has continuous approximating family $g_k$, then
--   $$\widehat{\mathcal G}=(G_n\circ\theta_n)\in\mathcal A(M),\qquad (g_k\circ\theta)_k\text{ is an approximating family}.$$
--   The transformation acts at the time-dependent reversal, not separately on each ergodic summand. This supplies the transformed potentials used in the fluctuation formulas.
-- source:
--   Fluctuation Theorem and Thermodynamic Formalism, arXiv:1712.05167v3, PDF p. 29, Lemma 3.6: transformation of asymptotically additive potentials

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

/-- Lemma 3.6, arXiv:1712.05167v3, PDF p.29. The time-dependent transformed
sequence has exactly the composed continuous approximants; all subsection
hypotheses USCE/WPS/S/PAP and the selected symmetry are retained. -/
theorem transformed_approximation (phi : M → M) (hphi : Continuous phi)
    (h : PeriodicHypotheses phi) (theta : M ≃ₜ M) (rev : Bool)
    (hsym : Symmetry phi theta rev) (G F : ℕ → M → ℝ)
    (hG : AsymptoticallyAdditive phi G) (hF : ApproximatingFamily phi G F) :
    AsymptoticallyAdditive phi (transformed phi theta rev G) ∧
      ApproximatingFamily phi (transformed phi theta rev G) (fun k x => F k (theta x)) := by sorry

end CompactDynamics

end QAlgorithms.Papers.Independent.Intake100.P82

end
