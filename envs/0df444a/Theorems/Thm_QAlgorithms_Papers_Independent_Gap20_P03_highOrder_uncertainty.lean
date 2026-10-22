-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P03_highOrder_uncertainty
-- name    : QAlgorithms.Papers.Independent.Gap20.P03.highOrder_uncertainty
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T20:13:36.215029+00:00
-- url     : https://prove2.me/theorems/9f6dc29e-c9df-4263-8274-4dda8824d906
-- title:
--   Theorem 3.3: general high-order entropic uncertainty relation (paper headline)
-- statement:
--   Let $n\ge0$, let $d\ge1$, and let $\mathcal B$ be a finite nonempty set of orthonormal bases of $\mathbb C^d$. Assume $h\ge0$ and that every single-system density state has average Shannon measurement entropy at least $h$ over $\mathcal B$. Let $\rho$ be any density state on $(\mathbb C^d)^{\otimes n}$, including mixed and entangled states. Independently of $\rho$, choose each component of $\Theta$ uniformly in $\mathcal B$, and measure to obtain $X$. For $0<\lambda<1/2$, put
--   $$\varepsilon=\exp\!\left(-\frac{\lambda^2 n}{32[\log_2(|\mathcal B|d/\lambda)]^2}\right).$$
--   Then
--   $$H_\infty^\varepsilon(X\mid\Theta)\ge(h-2\lambda)n.$$
--   Here smoothing deletes mass without renormalizing, and conditioning takes the worst supported original basis value. This converts a single-system Shannon uncertainty bound into high-order uncertainty for arbitrary multipartite states.
-- source:
--   A Tight High-Order Entropic Quantum Uncertainty Relation With Applications, arXiv:quant-ph/0612014v2, PDF p. 7, Theorem 3.3: general high-order entropic uncertainty relation (paper headline)

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P03

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap20.P03

open MeasureTheory Filter

open scoped ENNReal ComplexConjugate ComplexOrder Topology

-- Exact accepted finite Shannon entropy in bits (zero log zero is zero).

open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

attribute [local instance] Classical.propDecidable

/-- Theorem 3.3, pp.7-8. Bases form a finite nonempty set (injective indexing),
the single-system dimension is positive, and rho is an arbitrary density matrix. -/
theorem highOrder_uncertainty {I : Type} {B : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    [Fintype B] [Nonempty B] (bases : B → Matrix I I ℂ)
    (horth : ∀ b, bases b ∈ Matrix.unitaryGroup I ℂ) (hset : Function.Injective bases)
    (h : ℝ) (haverage : AverageUncertainty bases h) (n : ℕ)
    (rho : Matrix (Fin n → I) (Fin n → I) ℂ) (hrho : IsDensityMatrix rho)
    (lambda : ℝ) (hlambda : 0 < lambda) (hlambdaHalf : lambda < 1/2) :
    (((h-2*lambda)*n : ℝ) : EReal) ≤
      smoothMin (measurementExperiment bases rho) Prod.fst Prod.snd
        (accumulationError (Fintype.card B * Fintype.card I) n lambda) := by sorry

end QAlgorithms.Papers.Independent.Gap20.P03

end
