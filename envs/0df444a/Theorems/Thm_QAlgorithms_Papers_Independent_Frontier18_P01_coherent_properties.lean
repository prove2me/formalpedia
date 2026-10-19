-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P01_coherent_properties
-- name    : QAlgorithms.Papers.Independent.Frontier18.P01.coherent_properties
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:46:12.240986+00:00
-- url     : https://prove2.me/theorems/82dd3c3f-216d-44b1-8944-80a90b95c689
-- title:
--   Section 5 unnumbered: convexity, data processing and entropy bounds
-- statement:
--   All Hilbert spaces are complex and separable, with completed Hilbert tensor products. States are positive trace-class operators of trace one, and channels are completely positive and trace preserving. Write $H$ for entropy and $D$ for relative entropy, using natural logarithms; $I(\rho,\Phi)$ is the relative entropy of the channel-applied purification against the product of its marginals. Fix an input state $\rho$ with $H(\rho)<\infty$ and define $I_c(\rho,\Phi)=I(\rho,\Phi)-H(\rho)$. For $0\le t\le1$ and compatible channels,
--
--   $$\begin{aligned} I_c(\rho,t\Phi+(1-t)\Psi)&\le tI_c(\rho,\Phi)+(1-t)I_c(\rho,\Psi),\\ I_c(\rho,\Psi\circ\Phi)&\le I_c(\rho,\Phi),\\ -H(\rho)&\le I_c(\rho,\Phi)\le H(\rho).\end{aligned}$$
--
--   These are channel convexity, the first chain rule, and the two entropy bounds. No finite receiver-entropy assumption is needed.
-- source:
--   Mutual and coherent informations for infinite-dimensional quantum channels, arXiv:1004.2495v2, PDF p. 16, Section 5 unnumbered: convexity, data processing and entropy bounds

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P01

noncomputable section

open Filter

open scoped ENNReal

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Frontier18.P01

variable {I J K L E R : Type}

/-- Section 5, PDF p.16: convexity in the channel, FIRST chain rule, and both bounds. -/
theorem coherent_properties [Countable I] [Countable J] [Countable K] (rho : State I) (hin : homogeneousEntropy rho.coefficients < ⊤) :
    (∀ (Phi Psi : Channel I J) (t : ℝ), t ∈ Set.Icc 0 1 →
      finiteInputCoherentInfo rho.coefficients (fun X => convexOperatorMixture t (Phi.val X) (Psi.val X)) ≤
        t * finiteInputCoherentInfo rho.coefficients Phi.val + (1-t) * finiteInputCoherentInfo rho.coefficients Psi.val) ∧
    (∀ (Phi : Channel I J) (Psi : Channel J K),
      finiteInputCoherentInfo rho.coefficients (Psi.val ∘ Phi.val) ≤ finiteInputCoherentInfo rho.coefficients Phi.val) ∧
    (∀ Phi : Channel I J, -(homogeneousEntropy rho.coefficients).toReal ≤ finiteInputCoherentInfo rho.coefficients Phi.val ∧
      finiteInputCoherentInfo rho.coefficients Phi.val ≤ (homogeneousEntropy rho.coefficients).toReal) := by sorry

end QAlgorithms.Papers.Independent.Frontier18.P01

end
