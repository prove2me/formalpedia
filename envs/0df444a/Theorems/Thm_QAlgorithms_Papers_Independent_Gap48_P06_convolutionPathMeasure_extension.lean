-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P06_convolutionPathMeasure_extension
-- name    : QAlgorithms.Papers.Independent.Gap48.P06.convolutionPathMeasure_extension
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T21:05:25.261708+00:00
-- url     : https://prove2.me/theorems/aab0b28f-49b1-485d-bbb3-e49624d67942
-- title:
--   Consistent convolution path laws and their sigma-finite extension
-- statement:
--   Let $Q$ be a locally compact Polish topological group and $(\mu_t)_{t\ge0}$ a weakly continuous convolution semigroup of Borel probability measures with $\mu_0=\delta_1$. Let $\nu$ be a sigma-finite Borel measure satisfying $\nu*\mu_t=\nu$ for every $t>0$. Assume, as in the standing setup of Section 4.2, that $P_t f(x)=\int f(xy)\,d\mu_t(y)$ is symmetric on $L^2(Q,\nu)$: equivalently the joint law of $(x,xy)$ under $\nu(dx)\mu_t(dy)$ is invariant under swapping its two coordinates, for every $t\ge0$. For each nonempty nondecreasing real time tuple $t_1\le\cdots\le t_n$, define
--
--   $$P_t=(\psi_n)_*\bigl(\nu\otimes\mu_{t_2-t_1}\otimes\cdots\otimes\mu_{t_n-t_{n-1}}\bigr),\qquad\psi_n(x_1,\ldots,x_n)=(x_1,x_1x_2,\ldots,x_1\cdots x_n).$$
--
--   These measures are consistent under deletion of coordinates. There is a unique sigma-finite measure $P$ on $Q^{\mathbb R}$, with the coordinate-generated sigma-algebra, whose finite-dimensional marginals for strictly increasing tuples are $P_t$. The products are ordered as written; no commutativity is assumed. For one coordinate the law is $\nu$, and repeated times are governed by $\mu_0=\delta_1$. This provides the stationary path law even when the stationary measure has infinite mass.
-- source:
--   Reflection Positive Stochastic Processes Indexed by Lie Groups, arXiv:1510.07445v3, PDF p. 30, Lemma 4.8

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P06

noncomputable section

open MeasureTheory ProbabilityTheory Filter

open scoped Topology ENNReal NNReal

namespace QAlgorithms.Papers.Independent.Gap48.P06

/-- Lemma 4.8, PDF p.30: consistency of the explicit finite laws and unique
sigma-finite extension to the cylinder sigma-algebra on all paths. Standing
Polish/local-compactness and weak continuity assumptions come from Section 4.2.
Symmetry of the convolution operators from the Section 4.2 preamble is encoded
by symmetry of the actual two-time joint measures. The stationary measure may
have infinite mass and need not itself be invariant under group inversion. -/
theorem convolutionPathMeasure_extension
    {Q : Type*} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
    [PolishSpace Q] [LocallyCompactSpace Q] [MeasurableSpace Q] [BorelSpace Q]
    (mu : ℝ≥0 → Measure Q) (hprob : ∀ t, IsProbabilityMeasure (mu t))
    (hzero : mu 0 = Measure.dirac 1)
    (hsemigroup : ∀ s t, rightConvolution (mu s) (mu t) = mu (s + t))
    (hweak : ∀ f : Q → ℝ, Continuous f → Bornology.IsBounded (Set.range f) →
      Tendsto (fun t => ∫ x, f x ∂mu t) (𝓝 (0 : ℝ≥0)) (𝓝 (f 1)))
    (nu : Measure Q) [SigmaFinite nu]
    (hstationary : ∀ t : ℝ≥0, 0 < t → rightConvolution nu (mu t) = nu)
    (hbalance : ∀ t : ℝ≥0,
      Measure.map (fun z : Q × Q => (z.1 * z.2, z.1)) (nu.prod (mu t)) =
        Measure.map (fun z : Q × Q => (z.1, z.1 * z.2)) (nu.prod (mu t))) :
    (∀ (n m : ℕ) (t : Fin (n + 1) → ℝ), Monotone t →
      ∀ k : Fin (m + 1) → Fin (n + 1), StrictMono k →
        Measure.map (fun x i => x (k i)) (convolutionTupleLaw nu mu n t) =
          convolutionTupleLaw nu mu m (fun i => t (k i))) ∧
    (∃! rho : Measure (ℝ → Q), SigmaFinite rho ∧
      ∀ (n : ℕ) (t : Fin (n + 1) → ℝ), StrictMono t →
        Measure.map (fun w i => w (t i)) rho = convolutionTupleLaw nu mu n t) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P06

end
