-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P82_variation_and_terminal_deletion
-- name    : QAlgorithms.Papers.Independent.Intake100.P82.variation_and_terminal_deletion
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:13:46.831505+00:00
-- url     : https://prove2.me/theorems/9323735c-cb1a-45f0-8049-f9da8b64f0c6
-- title:
--   Lemma 2.5: variation and deletion of sublinear terminal segments
-- statement:
--   Let $M$ be a nonempty compact metric space with its Borel sigma-algebra, and let $\varphi:M\to M$ be continuous. Write $\mathcal P(M)$ for Borel probabilities with the weak topology, $\mathcal P_\varphi(M)$ for invariant probabilities, and $\mathcal E_\varphi(M)$ for ergodic probabilities. Entropy $h_\varphi$ is Kolmogorov–Sinai entropy with natural logarithms. For a bounded Borel sequence $\mathcal G=(G_n)_{n\ge1}$, asymptotic additivity means uniform approximation at linear scale by sums $S_n g=\sum_{j=0}^{n-1}g\circ\varphi^j$ of continuous functions. For such a sequence, $\mathcal G(Q)$ denotes the constructed real limit of $n^{-1}\int G_n\,dQ$ on invariant probabilities, and $p(\mathcal G)$ denotes its topological pressure. All time limits use positive integers.
--
--   Let $\mathcal G\in\mathcal A(M)$ and let $B_n(x,\delta)=\{y:d(\varphi^j y,\varphi^j x)<\delta,\ 0\le j<n\}$. Then
--   $$\lim_{\delta\downarrow0}\limsup_{n\to\infty}\frac1n\sup_x\sup_{y,z\in B_n(x,\delta)}|G_n(y)-G_n(z)|=0.$$
--   For any nonnegative integer deletion schedule $m_\delta(n)$ with $\lim_{\delta\downarrow0}\limsup_n m_\delta(n)/n=0$, both
--   $$\lim_{\delta\downarrow0}\limsup_n\frac{\|G_{n-m_\delta(n)}-G_n\|_\infty}{n}=0,$$
--   $$\lim_{\delta\downarrow0}\limsup_n\frac1n\sup_x\sup_{y,z\in B_{n-m_\delta(n)}(x,\delta)}|G_n(y)-G_n(z)|=0.$$
--   Shortened times are positive eventually at sufficiently small radii. The result controls deletion of sublinear terminal pieces, with the precise iterated limits.
-- source:
--   Fluctuation Theorem and Thermodynamic Formalism, arXiv:1712.05167v3, PDF p. 21, Lemma 2.5: variation and deletion of sublinear terminal segments

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

/-- Lemma 2.5, arXiv:1712.05167v3, PDF p.21. All three absolute-value
oscillation/deletion limits, with the shortened ball in (2.9). Only eventual
positive shortened times matter; no condition is imposed on a finite prefix. -/
theorem variation_and_terminal_deletion (phi : M → M) (hphi : Continuous phi)
    (G : ℕ → M → ℝ) (hG : AsymptoticallyAdditive phi G) :
    TemperedVariation phi G ∧
    ∀ m : ℝ → ℕ → ℕ,
      Tendsto (fun e : ℝ => limsup (fun n : ℕ =>
        ((m e (n + 1) : ℝ) / ((n + 1 : ℕ) : ℝ) : EReal)) atTop)
        (𝓝[>] (0 : ℝ)) (𝓝 0) →
      Tendsto (fun e : ℝ => limsup (fun n : ℕ =>
        (supNorm (fun x => G ((n + 1) - m e (n + 1)) x - G (n + 1) x) /
          ((n + 1 : ℕ) : ℝ) : EReal)) atTop) (𝓝[>] (0 : ℝ)) (𝓝 0) ∧
      Tendsto (fun e : ℝ => limsup (fun n : ℕ =>
        (bowenOscillation phi (G (n + 1)) ((n + 1) - m e (n + 1)) e /
          ((n + 1 : ℕ) : ℝ) : EReal)) atTop) (𝓝[>] (0 : ℝ)) (𝓝 0) := by sorry

end CompactDynamics

end QAlgorithms.Papers.Independent.Intake100.P82

end
