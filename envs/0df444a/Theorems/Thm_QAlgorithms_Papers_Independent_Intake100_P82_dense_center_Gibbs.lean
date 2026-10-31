-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P82_dense_center_Gibbs
-- name    : QAlgorithms.Papers.Independent.Intake100.P82.dense_center_Gibbs
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:19:28.991816+00:00
-- url     : https://prove2.me/theorems/28e256ed-b6de-4315-ac9d-e503b3a126cb
-- title:
--   Lemma 4.3: dense-center Gibbs estimates suffice
-- statement:
--   Let $M$ be a nonempty compact metric space with its Borel sigma-algebra, and let $\varphi:M\to M$ be continuous. Write $\mathcal P(M)$ for Borel probabilities with the weak topology, $\mathcal P_\varphi(M)$ for invariant probabilities, and $\mathcal E_\varphi(M)$ for ergodic probabilities. Entropy $h_\varphi$ is Kolmogorov–Sinai entropy with natural logarithms. For a bounded Borel sequence $\mathcal G=(G_n)_{n\ge1}$, asymptotic additivity means uniform approximation at linear scale by sums $S_n g=\sum_{j=0}^{n-1}g\circ\varphi^j$ of continuous functions. For such a sequence, $\mathcal G(Q)$ denotes the constructed real limit of $n^{-1}\int G_n\,dQ$ on invariant probabilities, and $p(\mathcal G)$ denotes its topological pressure. All time limits use positive integers.
--
--   Let $\mathcal G\in\mathcal A(M)$ have finite pressure and $P\in\mathcal P(M)$. Suppose there are dense sets $A_\epsilon$ and constants $K_n(\epsilon)\ge1$, uniform over centers, such that for every positive $\epsilon,n$ and every $x\in A_\epsilon$,
--   $$K_n(\epsilon)^{-1}e^{G_n(x)-np(\mathcal G)}\le P(B_n(x,\epsilon))\le K_n(\epsilon)e^{G_n(x)-np(\mathcal G)},$$
--   with $\lim_{\epsilon\downarrow0}\limsup_n n^{-1}\log K_n(\epsilon)=0$. Then $P$ is weak Gibbs for $\mathcal G$, meaning the same kind of bounds hold at all centers. This permits radius-dependent dense sets, without replacing density by an arbitrary almost-everywhere condition.
-- source:
--   Fluctuation Theorem and Thermodynamic Formalism, arXiv:1712.05167v3, PDF p. 31, Lemma 4.3: dense-center Gibbs estimates suffice

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

/-- Lemma 4.3, arXiv:1712.05167v3, PDF p.31. Dense centers may depend on
radius; the constants are uniform over centers and have the exact iterated limit. -/
theorem dense_center_Gibbs (phi : M → M) (hphi : Continuous phi)
    (G : ℕ → M → ℝ) (hG : AsymptoticallyAdditive phi G)
    (hp : FinitePressure phi G) (P : ProbabilityMeasure M)
    (A : ℝ → Set M) (hdense : ∀ e : ℝ, 0 < e → Dense (A e))
    (K : ℝ → ℕ → ℝ) (hK : GibbsBounds phi G P K A) :
    WeakGibbs phi G P := by sorry

end CompactDynamics

end QAlgorithms.Papers.Independent.Intake100.P82

end
