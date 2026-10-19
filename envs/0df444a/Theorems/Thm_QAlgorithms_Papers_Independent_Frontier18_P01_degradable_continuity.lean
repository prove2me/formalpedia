-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P01_degradable_continuity
-- name    : QAlgorithms.Papers.Independent.Frontier18.P01.degradable_continuity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:57:39.638988+00:00
-- url     : https://prove2.me/theorems/a3e5e237-6be6-4c5f-8c82-0beb80f31ac3
-- title:
--   Section 6 unnumbered: finiteness, uniform approximation and continuity equivalences for degradable channels
-- statement:
--   All Hilbert spaces are complex and separable, with completed Hilbert tensor products. States are positive trace-class operators of trace one, and channels are completely positive and trace preserving. Write $H$ for entropy and $D$ for relative entropy, using natural logarithms; $I(\rho,\Phi)$ is the relative entropy of the channel-applied purification against the product of its marginals. Let $\Phi,\widetilde\Phi$ be complementary and assume there is a CPTP channel $\Lambda$ with $\widetilde\Phi=\Lambda\circ\Phi$. Then
--
--   $$I(\rho,\Phi)<\infty\quad\Longleftrightarrow\quad H(\rho)<\infty.$$
--
--   For every subset $A$, finite-valued uniform convergence of the rank-constrained entropy approximators $H_k$ to $H$ is equivalent to that of $I_k$ to $I(\cdot,\Phi)$. Moreover, whenever $\rho_n\to\rho_0$ in trace norm,
--
--   $$H(\rho_n)\to H(\rho_0)<\infty\quad\Longleftrightarrow\quad I(\rho_n,\Phi)\to I(\rho_0,\Phi)<\infty.$$
--
--   The sequences may have extended values; the displayed limits are finite. These equivalences express necessity of the input-entropy continuity condition for degradable channels.
-- source:
--   Mutual and coherent informations for infinite-dimensional quantum channels, arXiv:1004.2495v2, PDF p. 21, Section 6 unnumbered: finiteness, uniform approximation and continuity equivalences for degradable channels

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P01

noncomputable section

open Filter

open scoped ENNReal

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Frontier18.P01

variable {I J K L E R : Type}

/-- Degradable-channel paragraph, PDF p.21: finiteness equivalence, reversal of
(30), and BOTH directions of the sequential continuity equivalence. -/
theorem degradable_continuity [Countable I] [Countable J] [Countable E] (Phi : Channel I J) (Psi : Channel I E)
    (hcomp : Complementary Phi Psi)
    (hdegrade : ∃ Lambda : Channel J E, ∀ rho : State I,
      Psi.val rho.coefficients = Lambda.val (Phi.val rho.coefficients)) :
    (∀ rho : State I, mutualInformation rho.coefficients Phi.val < ⊤ ↔ homogeneousEntropy rho.coefficients < ⊤) ∧
    (∀ A : Set (State I),
      UniformApprox A (fun rho => homogeneousEntropy rho.coefficients)
        (fun k rho => entropyApprox k rho.coefficients) ↔
      UniformApprox A (fun rho => mutualInformation rho.coefficients Phi.val)
        (fun k rho => mutualApprox k rho.coefficients Phi.val)) ∧
    (∀ (rho : ℕ → State I) (rho0 : State I), Tendsto rho atTop (nhds rho0) →
      ((Tendsto (fun n => homogeneousEntropy (rho n).coefficients) atTop
          (nhds (homogeneousEntropy rho0.coefficients)) ∧ homogeneousEntropy rho0.coefficients < ⊤) ↔
       (Tendsto (fun n => mutualInformation (rho n).coefficients Phi.val) atTop
          (nhds (mutualInformation rho0.coefficients Phi.val)) ∧ mutualInformation rho0.coefficients Phi.val < ⊤))) := by sorry

end QAlgorithms.Papers.Independent.Frontier18.P01

end
