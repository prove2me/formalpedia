-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P82_expansiveness_USCE_PAP
-- name    : QAlgorithms.Papers.Independent.Intake100.P82.expansiveness_USCE_PAP
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:14:53.117526+00:00
-- url     : https://prove2.me/theorems/0b351ddc-8471-4eaf-bc5d-59d9b5fa2af4
-- title:
--   Theorem 2.8: expansiveness implies USCE and periodic pressure approximation
-- statement:
--   Let $M$ be a nonempty compact metric space with its Borel sigma-algebra, and let $\varphi:M\to M$ be continuous. Write $\mathcal P(M)$ for Borel probabilities with the weak topology, $\mathcal P_\varphi(M)$ for invariant probabilities, and $\mathcal E_\varphi(M)$ for ergodic probabilities. Entropy $h_\varphi$ is Kolmogorov–Sinai entropy with natural logarithms. For a bounded Borel sequence $\mathcal G=(G_n)_{n\ge1}$, asymptotic additivity means uniform approximation at linear scale by sums $S_n g=\sum_{j=0}^{n-1}g\circ\varphi^j$ of continuous functions. For such a sequence, $\mathcal G(Q)$ denotes the constructed real limit of $n^{-1}\int G_n\,dQ$ on invariant probabilities, and $p(\mathcal G)$ denotes its topological pressure. All time limits use positive integers.
--
--   Condition USCE means finite topological entropy and upper semicontinuity of $Q\mapsto h_\varphi(Q)$ on invariant probabilities. S is ordinary specification; WPS is the source weak periodic specification; PAP is finiteness of periodic sets and convergence of their normalized log partition sums to pressure.
--
--   If $\varphi$ is forward expansive, or is an expansive homeomorphism, then
--   $$\mathrm{USCE}\text{ holds},\qquad\mathrm{WPS}\Longrightarrow\mathrm{PAP}.$$
--   Forward expansiveness separates points using nonnegative iterates; homeomorphism expansiveness uses all integer iterates. The two branches are distinct and neither S nor potential regularity is assumed. Thus entropy regularity and periodic pressure approximation are derived from expansiveness.
-- source:
--   Fluctuation Theorem and Thermodynamic Formalism, arXiv:1712.05167v3, PDF p. 25, Theorem 2.8: expansiveness implies USCE and periodic pressure approximation

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

/-- Theorem 2.8, arXiv:1712.05167v3, PDF p.25. Forward continuous maps
and two-sided homeomorphisms are separate branches. USCE/PAP are conclusions;
WPS is required only for the second conclusion in each branch. -/
theorem expansiveness_USCE_PAP :
    (∀ phi : M → M, Continuous phi → ForwardExpansive phi →
      USCE phi ∧ (WPS phi → PAP phi)) ∧
    (∀ f : M ≃ₜ M, Expansive f → USCE f ∧ (WPS f → PAP f)) := by sorry

end CompactDynamics

end QAlgorithms.Papers.Independent.Intake100.P82

end
