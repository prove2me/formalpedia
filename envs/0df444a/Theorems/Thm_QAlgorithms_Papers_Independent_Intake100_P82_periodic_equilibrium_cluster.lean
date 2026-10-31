-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P82_periodic_equilibrium_cluster
-- name    : QAlgorithms.Papers.Independent.Intake100.P82.periodic_equilibrium_cluster
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:15:27.201987+00:00
-- url     : https://prove2.me/theorems/b1979d7a-a417-419c-bcc6-3de034263c40
-- title:
--   Proposition 2.9: Cesaro periodic laws converge to equilibrium states
-- statement:
--   Let $M$ be a nonempty compact metric space with its Borel sigma-algebra, and let $\varphi:M\to M$ be continuous. Write $\mathcal P(M)$ for Borel probabilities with the weak topology, $\mathcal P_\varphi(M)$ for invariant probabilities, and $\mathcal E_\varphi(M)$ for ergodic probabilities. Entropy $h_\varphi$ is Kolmogorov–Sinai entropy with natural logarithms. For a bounded Borel sequence $\mathcal G=(G_n)_{n\ge1}$, asymptotic additivity means uniform approximation at linear scale by sums $S_n g=\sum_{j=0}^{n-1}g\circ\varphi^j$ of continuous functions. For such a sequence, $\mathcal G(Q)$ denotes the constructed real limit of $n^{-1}\int G_n\,dQ$ on invariant probabilities, and $p(\mathcal G)$ denotes its topological pressure. All time limits use positive integers.
--
--   Condition USCE means finite topological entropy and upper semicontinuity of $Q\mapsto h_\varphi(Q)$ on invariant probabilities. S is ordinary specification; WPS is the source weak periodic specification; PAP is finiteness of periodic sets and convergence of their normalized log partition sums to pressure.
--
--   For $M_n=\operatorname{Fix}(\varphi^n)$ finite and nonempty, put $Z_n=\sum_{x\in M_n}e^{G_n(x)}$ and $P_n=Z_n^{-1}\sum_{x\in M_n}e^{G_n(x)}\delta_x$. At the finitely many unused early times with empty periodic sets, use a fixed reference Dirac law. This extension has no effect on any asymptotic assertion.
--
--   Assume USCE and PAP and let $\mathcal G\in\mathcal A(M)$. Every weak subsequential limit of
--   $$\overline P_n=\frac1n\sum_{j=0}^{n-1}(\varphi^j)_*P_n$$
--   is an equilibrium probability: it is invariant and $p(\mathcal G)=\mathcal G(P)+h_\varphi(P)$. In the additive case $G_n=S_ng$, the averaging changes no law at a positive time with nonempty periodic set, and every weak cluster point of $P_n$ is equilibrium. The arbitrary finite initial extension is irrelevant to cluster limits. This explains why Cesaro averaging is required for general nonadditive potentials.
-- source:
--   Fluctuation Theorem and Thermodynamic Formalism, arXiv:1712.05167v3, PDF p. 26, Proposition 2.9: Cesaro periodic laws converge to equilibrium states

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

/-- Proposition 2.9, arXiv:1712.05167v3, PDF p.26. Averaged laws are used
for arbitrary AA sequences. In the additive case averaging changes no positive-time
periodic law on a nonempty periodic set, and every cluster law is equilibrium.
An arbitrary finite initial extension need not itself be invariant. -/
theorem periodic_equilibrium_cluster (phi : M → M) (hphi : Continuous phi)
    (hu : USCE phi) (hp : PAP phi) (G : ℕ → M → ℝ)
    (hG : AsymptoticallyAdditive phi G) (reference : M) :
    (∀ P : ProbabilityMeasure M, WeakCluster (averagedPeriodicLaw phi G reference) P →
      Equilibrium phi G P) ∧
    ∀ g : C(M, ℝ),
      (∀ n : ℕ, 1 ≤ n → (periodicSet phi n).Nonempty →
        averagedPeriodicLaw phi (orbitSum phi g) reference n =
          periodicLaw phi (orbitSum phi g) reference n) ∧
      (∀ P : ProbabilityMeasure M, WeakCluster (periodicLaw phi (orbitSum phi g) reference) P →
        Equilibrium phi (orbitSum phi g) P) := by sorry

end CompactDynamics

end QAlgorithms.Papers.Independent.Intake100.P82

end
