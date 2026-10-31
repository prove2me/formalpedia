-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P82_periodic_partition_RN_symmetry
-- name    : QAlgorithms.Papers.Independent.Intake100.P82.periodic_partition_RN_symmetry
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:17:23.22793+00:00
-- url     : https://prove2.me/theorems/af5bf4e0-2e45-4fd5-9b7e-58a88a32e85d
-- title:
--   Lemma 3.8: periodic partition symmetry and exact entropy density
-- statement:
--   Let $M$ be a nonempty compact metric space with its Borel sigma-algebra, and let $\varphi:M\to M$ be continuous. Write $\mathcal P(M)$ for Borel probabilities with the weak topology, $\mathcal P_\varphi(M)$ for invariant probabilities, and $\mathcal E_\varphi(M)$ for ergodic probabilities. Entropy $h_\varphi$ is Kolmogorov–Sinai entropy with natural logarithms. For a bounded Borel sequence $\mathcal G=(G_n)_{n\ge1}$, asymptotic additivity means uniform approximation at linear scale by sums $S_n g=\sum_{j=0}^{n-1}g\circ\varphi^j$ of continuous functions. For such a sequence, $\mathcal G(Q)$ denotes the constructed real limit of $n^{-1}\int G_n\,dQ$ on invariant probabilities, and $p(\mathcal G)$ denotes its topological pressure. All time limits use positive integers.
--
--   Condition USCE means finite topological entropy and upper semicontinuity of $Q\mapsto h_\varphi(Q)$ on invariant probabilities. S is ordinary specification; WPS is the source weak periodic specification; PAP is finiteness of periodic sets and convergence of their normalized log partition sums to pressure.
--
--   Choose either C-Commutation, where $\theta$ is an involutive homeomorphism and $\varphi=\theta\circ\varphi\circ\theta$, or R-Reversal, where additionally $\varphi$ is a homeomorphism and $\varphi^{-1}=\theta\circ\varphi\circ\theta$. Set $\theta_n=\theta$ in C and $\theta_n=\theta\circ\varphi^{n-1}$ in R, $\widehat G_n=G_n\circ\theta_n$, $\sigma_n=G_n-\widehat G_n$, and $\operatorname{ep}(Q)=\mathcal G(Q)-\mathcal G(\theta_*Q)$ for invariant $Q$.
--
--   For $M_n=\operatorname{Fix}(\varphi^n)$ finite and nonempty, put $Z_n=\sum_{x\in M_n}e^{G_n(x)}$ and $P_n=Z_n^{-1}\sum_{x\in M_n}e^{G_n(x)}\delta_x$. At the finitely many unused early times with empty periodic sets, use a fixed reference Dirac law. This extension has no effect on any asymptotic assertion.
--
--   Retain USCE, WPS, S and PAP, and fix a positive time $n$ with $M_n$ finite and nonempty. For every AA potential,
--   $$Z_n(\mathcal G)=Z_n(\widehat{\mathcal G}),\qquad (\theta_n)_*P_n=Z_n^{-1}\sum_{x\in M_n}e^{G_n(\theta_n x)}\delta_x.$$
--   The two probabilities are mutually absolutely continuous and
--   $$\log\frac{dP_n}{d((\theta_n)_*P_n)}=\sigma_n\quad P_n\text{-almost everywhere}.$$
--   This is the exact finite-time identity. The nonempty-period domain is essential and is not replaced by normalization of the zero measure.
-- source:
--   Fluctuation Theorem and Thermodynamic Formalism, arXiv:1712.05167v3, PDF p. 29, Lemma 3.8: periodic partition symmetry and exact entropy density

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

/-- Lemma 3.8, arXiv:1712.05167v3, PDF p.29. Finite NONEMPTY periodic set
is the finite-time domain: equal partitions, explicit reversed law, mutual absolute
continuity, and a.e. log RN derivative, all included. -/
theorem periodic_partition_RN_symmetry (phi : M → M) (hphi : Continuous phi)
    (h : PeriodicHypotheses phi) (theta : M ≃ₜ M) (rev : Bool)
    (hsym : Symmetry phi theta rev) (G : ℕ → M → ℝ)
    (hG : AsymptoticallyAdditive phi G) (reference : M)
    (n : ℕ) (hn : 1 ≤ n) (hf : (periodicSet phi n).Finite)
    (hne : (periodicSet phi n).Nonempty) :
    let P := periodicLaw phi G reference n
    let Phat := Measure.map (timeReversal phi theta rev n) P
    periodicPartition phi G n = periodicPartition phi (transformed phi theta rev G) n ∧
    Phat = (periodicPartition phi G n)⁻¹ •
      ∑ x ∈ hf.toFinset,
        ENNReal.ofReal (Real.exp (G n (timeReversal phi theta rev n x))) • Measure.dirac x ∧
    P ≪ Phat ∧ Phat ≪ P ∧
    (∀ᵐ x ∂P, Real.log ((P.rnDeriv Phat x).toReal) = sequenceEntropyProduction phi theta rev G n x) := by sorry

end CompactDynamics

end QAlgorithms.Papers.Independent.Intake100.P82

end
