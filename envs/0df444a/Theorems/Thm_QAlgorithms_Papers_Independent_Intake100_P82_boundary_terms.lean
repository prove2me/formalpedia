-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P82_boundary_terms
-- name    : QAlgorithms.Papers.Independent.Intake100.P82.boundary_terms
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:08:17.217181+00:00
-- url     : https://prove2.me/theorems/862f8b0b-95ce-4112-a2b2-12d772adc181
-- title:
--   Example 0.14: boundary terms in finite spin chains
-- statement:
--   Let $M$ be a nonempty compact metric space with its Borel sigma-algebra, and let $\varphi:M\to M$ be continuous. Write $\mathcal P(M)$ for Borel probabilities with the weak topology, $\mathcal P_\varphi(M)$ for invariant probabilities, and $\mathcal E_\varphi(M)$ for ergodic probabilities. Entropy $h_\varphi$ is Kolmogorov–Sinai entropy with natural logarithms. For a bounded Borel sequence $\mathcal G=(G_n)_{n\ge1}$, asymptotic additivity means uniform approximation at linear scale by sums $S_n g=\sum_{j=0}^{n-1}g\circ\varphi^j$ of continuous functions. For such a sequence, $\mathcal G(Q)$ denotes the constructed real limit of $n^{-1}\int G_n\,dQ$ on invariant probabilities, and $p(\mathcal G)$ denotes its topological pressure. All time limits use positive integers.
--
--   Assume $\varphi$ is an expansive homeomorphism satisfying Bowen specification. Let $\theta$ be a continuous involution with $\varphi^{-1}=\theta\circ\varphi\circ\theta$. No regularity of the potential beyond that stated, uniqueness of equilibrium, or ergodicity is assumed.
--
--   For $M_n=\operatorname{Fix}(\varphi^n)$ finite and nonempty, put $Z_n=\sum_{x\in M_n}e^{G_n(x)}$ and $P_n=Z_n^{-1}\sum_{x\in M_n}e^{G_n(x)}\delta_x$. At the finitely many unused early times with empty periodic sets, use a fixed reference Dirac law. This extension has no effect on any asymptotic assertion.
--
--   Assume $M$ is a full two-sided finite-alphabet shift. Let $g=A_\Phi$ be the given continuous onsite potential, and let $b_n$ be bounded Borel boundary terms satisfying $\|b_n\|_\infty/n\to0$. Then
--   $$G_n=S_n g+b_n\in\mathcal A(M),\qquad (G_n)\sim(S_n g).$$
--   Consequently the empirical/scalar LDP and fluctuation principle of the asymptotically additive extension hold for the finite-size periodic laws defined by $G_n$. Here equivalence means $\|G_n-S_n g\|_\infty/n\to0$. This isolates the boundary correction; it assumes the continuous onsite potential rather than asserting a construction of interactions or infinite-volume Gibbs states. Finite configurations are identified with fixed points, not primitive cyclic orbit classes.
-- source:
--   Fluctuation Theorem and Thermodynamic Formalism, arXiv:1712.05167v3, PDF p. 9, Example 0.14: boundary terms in finite spin chains

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

/-- Example 0.14, arXiv:1712.05167v3, PDF p.9. The explicit boundary-term
consequence for a given continuous onsite potential; no external construction
of the interaction energy or classification of infinite-volume Gibbs states.
Finite chains correspond to fixed points, never cyclic-shift equivalence classes. -/
theorem boundary_terms (f theta : M ≃ₜ M) (h : IntroHypotheses f theta)
    (hfull : FullShift f) (g : C(M, ℝ)) (b : ℕ → M → ℝ)
    (hb : BorelSequence b)
    (hsub : Tendsto (fun n : ℕ => supNorm (b (n + 1)) / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 0))
    (reference : M) :
    let G := fun n x => orbitSum f g n x + b n x
    AsymptoticallyAdditive f G ∧ EquivalentPotentials G (orbitSum f g) ∧
      EmpiricalScalarLDP f G (periodicLaw f G reference) ∧
      FluctuationPrinciple f G theta true (periodicLaw f G reference) := by sorry

end CompactDynamics

end QAlgorithms.Papers.Independent.Intake100.P82

end
