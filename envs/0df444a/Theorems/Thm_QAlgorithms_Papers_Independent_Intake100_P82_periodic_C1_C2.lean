-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P82_periodic_C1_C2
-- name    : QAlgorithms.Papers.Independent.Intake100.P82.periodic_C1_C2
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:23:10.464809+00:00
-- url     : https://prove2.me/theorems/f9102679-b50b-4667-95dd-66a508995903
-- title:
--   Lemma 5.3: periodic laws satisfy C1 and C2
-- statement:
--   Let $M$ be a nonempty compact metric space with its Borel sigma-algebra, and let $\varphi:M\to M$ be continuous. Write $\mathcal P(M)$ for Borel probabilities with the weak topology, $\mathcal P_\varphi(M)$ for invariant probabilities, and $\mathcal E_\varphi(M)$ for ergodic probabilities. Entropy $h_\varphi$ is Kolmogorov–Sinai entropy with natural logarithms. For a bounded Borel sequence $\mathcal G=(G_n)_{n\ge1}$, asymptotic additivity means uniform approximation at linear scale by sums $S_n g=\sum_{j=0}^{n-1}g\circ\varphi^j$ of continuous functions. For such a sequence, $\mathcal G(Q)$ denotes the constructed real limit of $n^{-1}\int G_n\,dQ$ on invariant probabilities, and $p(\mathcal G)$ denotes its topological pressure. All time limits use positive integers.
--
--   Condition USCE means finite topological entropy and upper semicontinuity of $Q\mapsto h_\varphi(Q)$ on invariant probabilities. S is ordinary specification; WPS is the source weak periodic specification; PAP is finiteness of periodic sets and convergence of their normalized log partition sums to pressure.
--
--   For $M_n=\operatorname{Fix}(\varphi^n)$ finite and nonempty, put $Z_n=\sum_{x\in M_n}e^{G_n(x)}$ and $P_n=Z_n^{-1}\sum_{x\in M_n}e^{G_n(x)}\delta_x$. At the finitely many unused early times with empty periodic sets, use a fixed reference Dirac law. This extension has no effect on any asymptotic assertion.
--
--   Assume WPS and PAP, on the finite-topological-entropy domain of the real pressure differences in Section 5.1, and let $\mathcal G\in\mathcal A(M)$. The periodic laws satisfy both conditions:
--
--   For every $v\in C(M)$ assume C1,
--   $$\frac1n\log\int e^{S_nv}\,dP_n\longrightarrow p(\mathcal G+Sv)-p(\mathcal G).$$
--   Assume C2: for every sufficiently small positive $\delta$ there are $n_0(\delta)\ge1$, $K_n(\delta)\ge1$ and integers $0\le m_\delta(n)<n$ on the eventual time domain such that, uniformly in $x$,
--   $$K_n(\delta)^{-1}e^{G_n(x)-np(\mathcal G)}\le P_n(B_{n-m_\delta(n)}(x,\delta)),\quad n\ge n_0(\delta),$$
--   $$\lim_{\delta\downarrow0}\limsup_n\frac{\log K_n(\delta)+m_\delta(n)}n=0.$$
--   The witnesses depend on radius and time, never on the center.
--
--   Thus C1 and C2 hold for the actual weighted periodic laws; no LDP is assumed. The finite-pressure domain is explicit.
-- source:
--   Fluctuation Theorem and Thermodynamic Formalism, arXiv:1712.05167v3, PDF p. 34, Lemma 5.3: periodic laws satisfy C1 and C2

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

/-- Lemma 5.3, arXiv:1712.05167v3, PDF p.34. Finite-pressure domain of C1/C2
is retained. The printed proof's n-prime partition typo is not a new assumption. -/
theorem periodic_C1_C2 (phi : M → M) (hphi : Continuous phi)
    (hw : WPS phi) (hp : PAP phi) (hfinite : topologicalEntropy phi < ⊤)
    (G : ℕ → M → ℝ) (hG : AsymptoticallyAdditive phi G) (reference : M) :
    C1 phi G (periodicLaw phi G reference) ∧ C2 phi G (periodicLaw phi G reference) := by sorry

end CompactDynamics

end QAlgorithms.Papers.Independent.Intake100.P82

end
