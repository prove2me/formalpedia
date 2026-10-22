-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P06_reversibleMarkov_stationaryExtension
-- name    : QAlgorithms.Papers.Independent.Gap48.P06.reversibleMarkov_stationaryExtension
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T21:09:30.025809+00:00
-- url     : https://prove2.me/theorems/10a772e0-3325-4bdf-9128-6ad2c84ac341
-- title:
--   Two-sided stationary extension of a reversible Markov semigroup
-- statement:
--   Let $Q$ be a Polish space with its Borel sigma-algebra. Let $(P_t)_{t\ge0}$ be Markov kernels with $P_0$ the identity kernel and $P_{s+t}=P_sP_t$, and let $\nu$ be a probability measure satisfying detailed balance: $\nu(dx)P_t(x,dy)$ is unchanged by swapping $x$ and $y$. Then there is a probability law $P^\nu$ on the canonical path space $Q^{\mathbb R}$, invariant under all time shifts, with initial marginal $\nu$ and, for every strictly increasing tuple $t_1<\cdots<t_n$,
--
--   $$P^\nu((X_{t_1},\ldots,X_{t_n})\in B)=\int\!\mathbf1_B(x_1,\ldots,x_n)\,\nu(dx_1)P_{t_2-t_1}(x_1,dx_2)\cdots P_{t_n-t_{n-1}}(x_{n-1},dx_n).$$
--
--   Here $X_t(\omega)=\omega(t)$, and $B$ is any measurable cylinder target set. The finite laws are defined by the actual successive kernel integrals, not by assumed marginal identities. Detailed balance is the hypothesis that makes the two-sided construction stationary. No time continuity or second-moment assumption is needed. This constructs a stationary process from reversible Markov transition data.
-- source:
--   Reflection Positive Stochastic Processes Indexed by Lie Groups, arXiv:1510.07445v3, PDF p. 46, Appendix B, unnumbered: stationary extension to R

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P06

noncomputable section

open MeasureTheory ProbabilityTheory Filter

open scoped Topology ENNReal NNReal

namespace QAlgorithms.Papers.Independent.Gap48.P06

/-- Appendix B, unnumbered stationary extension, PDF pp.46--47: a reversible
Markov semigroup with a probability initial measure has a stationary two-sided
canonical process, with the displayed ordered cylinder laws. Detailed balance
is expressed as symmetry of the actual joint measure nu(dx)P_t(x,dy),
equivalently the source's nonnegative integral duality. No continuity in time
or second moment is assumed. -/
theorem reversibleMarkov_stationaryExtension
    {Q : Type*} [TopologicalSpace Q] [PolishSpace Q]
    [MeasurableSpace Q] [BorelSpace Q]
    (P : ℝ≥0 → Kernel Q Q) (hmarkov : ∀ t, IsMarkovKernel (P t))
    (hzero : P 0 = Kernel.id)
    (hsemigroup : ∀ s t, P (s + t) = (P t) ∘ₖ (P s))
    (nu : Measure Q) [IsProbabilityMeasure nu]
    (hbalance : ∀ t, Measure.map Prod.swap (nu ⊗ₘ P t) = nu ⊗ₘ P t) :
    ∃ rho : Measure (ℝ → Q), IsProbabilityMeasure rho ∧
      Measure.map (fun w => w 0) rho = nu ∧
      (∀ t : ℝ, MeasurePreserving (fun w s => w (s - t)) rho rho) ∧
      (∀ (n : ℕ) (t : Fin (n + 1) → ℝ), StrictMono t →
        Measure.map (fun w i => w (t i)) rho = orderedKernelLaw nu P n t) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P06

end
