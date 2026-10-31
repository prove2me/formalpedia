-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P82_fixed_offset_LDP
-- name    : QAlgorithms.Papers.Independent.Intake100.P82.fixed_offset_LDP
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:11:30.279422+00:00
-- url     : https://prove2.me/theorems/bd52389b-4699-42e3-a7e4-be6c0a1ebf4f
-- title:
--   Unnumbered result (1.12): fixed-offset periodic-law LDP
-- statement:
--   Let $M$ be a nonempty compact metric space with its Borel sigma-algebra, and let $\varphi:M\to M$ be continuous. Write $\mathcal P(M)$ for Borel probabilities with the weak topology, $\mathcal P_\varphi(M)$ for invariant probabilities, and $\mathcal E_\varphi(M)$ for ergodic probabilities. Entropy $h_\varphi$ is Kolmogorov–Sinai entropy with natural logarithms. For a bounded Borel sequence $\mathcal G=(G_n)_{n\ge1}$, asymptotic additivity means uniform approximation at linear scale by sums $S_n g=\sum_{j=0}^{n-1}g\circ\varphi^j$ of continuous functions. For such a sequence, $\mathcal G(Q)$ denotes the constructed real limit of $n^{-1}\int G_n\,dQ$ on invariant probabilities, and $p(\mathcal G)$ denotes its topological pressure. All time limits use positive integers.
--
--   Assume $\varphi$ is an expansive homeomorphism satisfying Bowen specification. Let $\theta$ be a continuous involution with $\varphi^{-1}=\theta\circ\varphi\circ\theta$. No regularity of the potential beyond that stated, uniqueness of equilibrium, or ergodicity is assumed.
--
--   For $M_n=\operatorname{Fix}(\varphi^n)$ finite and nonempty, put $Z_n=\sum_{x\in M_n}e^{G_n(x)}$ and $P_n=Z_n^{-1}\sum_{x\in M_n}e^{G_n(x)}\delta_x$. At the finitely many unused early times with empty periodic sets, use a fixed reference Dirac law. This extension has no effect on any asymptotic assertion.
--
--   Let $g\in C(M)$, $\sigma=g-g\circ\theta$, and let $I$ be the scalar contraction rate in Theorem A. For each fixed nonnegative integer $m$,
--   $$S_n\sigma/n\quad\text{under }P_{n+m}\quad\text{satisfies the full speed-}n\text{ LDP with rate }I.$$
--   The shift of the law is fixed before taking the time limit. This gives (1.12), with the interior/closure Borel-set bounds, and makes no assertion uniform in $m$.
-- source:
--   Fluctuation Theorem and Thermodynamic Formalism, arXiv:1712.05167v3, PDF p. 17, Unnumbered result (1.12): fixed-offset periodic-law LDP

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

/-- Fixed-offset LDP (1.12), arXiv:1712.05167v3, PDF p.17.
Each fixed m is outside the n limit; observable length n, law index n+m. -/
theorem fixed_offset_LDP (f theta : M ≃ₜ M) (h : IntroHypotheses f theta)
    (g : C(M, ℝ)) (reference : M) (m : ℕ) :
    FullLDP (scalarEvents (fun n => periodicLaw f (orbitSum f g) reference (n + m))
      (orbitSum f (fun x => g x - g (theta x))))
      (additiveScalarRate f g theta) := by sorry

end CompactDynamics

end QAlgorithms.Papers.Independent.Intake100.P82

end
