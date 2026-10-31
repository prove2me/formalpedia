-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P82_continuous_regularization
-- name    : QAlgorithms.Papers.Independent.Intake100.P82.continuous_regularization
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:26:56.662876+00:00
-- url     : https://prove2.me/theorems/4300539b-7217-4af8-bf67-710d13cf81b2
-- title:
--   Lemma 6.4: continuous regularization of locally small oscillation
-- statement:
--   Let $M$ be a nonempty compact metric space with its Borel sigma-algebra, and let $\varphi:M\to M$ be continuous. Write $\mathcal P(M)$ for Borel probabilities with the weak topology, $\mathcal P_\varphi(M)$ for invariant probabilities, and $\mathcal E_\varphi(M)$ for ergodic probabilities. Entropy $h_\varphi$ is Kolmogorov–Sinai entropy with natural logarithms. For a bounded Borel sequence $\mathcal G=(G_n)_{n\ge1}$, asymptotic additivity means uniform approximation at linear scale by sums $S_n g=\sum_{j=0}^{n-1}g\circ\varphi^j$ of continuous functions. For such a sequence, $\mathcal G(Q)$ denotes the constructed real limit of $n^{-1}\int G_n\,dQ$ on invariant probabilities, and $p(\mathcal G)$ denotes its topological pressure. All time limits use positive integers.
--
--   Let $f\in B(M)$, let $n\ge1$ be a finite integer and let $\epsilon>0$. Suppose, for a real $\alpha$,
--   $$\sup_{x\in M}\sup_{y\in B_n(x,\epsilon)}|f(y)-f(x)|\le\alpha.$$
--   Then there exists a continuous $g:M\to\mathbb R$ such that $\|f-g\|_\infty\le\alpha$. Here $B_n$ is the open Bowen ball. Nonnegativity of $\alpha$ follows from the bound on the nonempty space. The result regularizes a bounded Borel function without an asymptotic-additivity assumption.
-- source:
--   Fluctuation Theorem and Thermodynamic Formalism, arXiv:1712.05167v3, PDF p. 42, Lemma 6.4: continuous regularization of locally small oscillation

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

/-- Lemma 6.4, arXiv:1712.05167v3, PDF p.42. Positive radius and positive
finite time ensure the Bowen balls form an open cover. Alpha nonnegativity
follows from the bound on a nonempty space, rather than being an extra hypothesis. -/
theorem continuous_regularization (phi : M → M) (hphi : Continuous phi)
    (f : M → ℝ) (hf : BoundedBorel f) (n : ℕ) (hn : 1 ≤ n)
    (epsilon alpha : ℝ) (he : 0 < epsilon)
    (hosc : ∀ x : M, ∀ y ∈ bowenBall phi n x epsilon, |f y - f x| ≤ alpha) :
    ∃ g : C(M, ℝ), supNorm (fun x => f x - g x) ≤ alpha := by sorry

end CompactDynamics

end QAlgorithms.Papers.Independent.Intake100.P82

end
