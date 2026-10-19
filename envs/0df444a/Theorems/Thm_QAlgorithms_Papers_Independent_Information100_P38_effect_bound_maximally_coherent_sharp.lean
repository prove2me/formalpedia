-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P38_effect_bound_maximally_coherent_sharp
-- name    : QAlgorithms.Papers.Independent.Information100.P38.effect_bound_maximally_coherent_sharp
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T11:10:46.934214+00:00
-- url     : https://prove2.me/theorems/0b07e313-6f9b-4e58-8064-e0e22a3a9767
-- title:
--   Appendix A sharpness
-- statement:
--   Let $d\ge1$ and let $\psi$ be a unit vector in $\mathbb C^d$ with $|\psi_i|^2=1/d$ for every reference coordinate. The rank-one projector $A=|\psi\rangle\langle\psi|$ is an effect, $\Delta A=I/d$, and
--
--   $$\lambda_{\max}(A-\Delta A)=1-\frac1d.$$
--
--   Thus Lemma 1 is sharp in every positive dimension, including its zero bound for $d=1$. This is sharpness of the effect inequality; it does not by itself establish sharpness of the final measurement-advantage prefactor.
-- source:
--   All coherent measurements provide observational ergotropic advantage, arXiv:2609.18735v1, PDF p. 12, Appendix A sharpness

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P38

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P38

open scoped ComplexConjugate Matrix

/-- Paper p.12, Appendix A: sharpness of Lemma 1 at every maximally coherent rank-one
projector. This does not assert dimensional optimality of Theorem 3's final bound. -/
theorem effect_bound_maximally_coherent_sharp {d : ℕ} (hd : 0 < d)
    (v : EuclideanSpace ℂ (Fin d)) (hv : IsState v)
    (hc : ∀ i, Complex.normSq (v i) = 1 / (d : ℝ)) :
    IsEffect (pureDensity v) ∧ energyDephasing (pureDensity v) = ((1 / (d : ℝ) : ℝ) : ℂ) • 1 ∧
    largestEnergyEigenvalue (pureDensity v - energyDephasing (pureDensity v)) = 1 - 1 / (d : ℝ) := by sorry

end QAlgorithms.Papers.Independent.Information100.P38

end
