-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P01_convergent_purifications
-- name    : QAlgorithms.Papers.Independent.Frontier18.P01.convergent_purifications
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:43:41.316978+00:00
-- url     : https://prove2.me/theorems/9991c0f8-042e-48a2-a3a0-8ae0066e31fe
-- title:
--   Lemma 2: convergent purifications of convergent states
-- statement:
--   All Hilbert spaces are complex and separable, with completed Hilbert tensor products. States are positive trace-class operators of trace one, and channels are completely positive and trace preserving. Write $H$ for entropy and $D$ for relative entropy, using natural logarithms; $I(\rho,\Phi)$ is the relative entropy of the channel-applied purification against the product of its marginals. Suppose states $\rho_n$ converge in trace norm to $\rho_0$ on $\mathcal H$. There exist pure states $\widehat\rho_n$ and $\widehat\rho_0$ on $\mathcal H\otimes\mathcal H$ such that
--
--   $$\operatorname{Tr}_2\widehat\rho_n=\rho_n,\qquad \operatorname{Tr}_2\widehat\rho_0=\rho_0,\qquad \widehat\rho_n\longrightarrow\widehat\rho_0\quad\text{in trace norm}.$$
--
--   Both the sequence and its limit are existential. This gives convergent density-operator purifications without imposing convergence of chosen vector phases.
-- source:
--   Mutual and coherent informations for infinite-dimensional quantum channels, arXiv:1004.2495v2, PDF p. 10, Lemma 2: convergent purifications of convergent states

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P01

noncomputable section

open Filter

open scoped ENNReal

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Frontier18.P01

variable {I J K L E R : Type}

/-- Lemma 2, PDF p.10. Both the purification sequence and its limit are existential;
convergence is trace norm on pure density operators, without a fixed-phase demand. -/
theorem convergent_purifications [Countable I] (rho : ℕ → State I) (rho0 : State I)
    (h : Tendsto rho atTop (nhds rho0)) :
    ∃ (psi : ℕ → PureState (I × I)) (psi0 : PureState (I × I)),
      (∀ n, Purifies (psi n) (rho n).coefficients) ∧ Purifies psi0 rho0.coefficients ∧
      Tendsto (fun n => (psi n).val) atTop (nhds psi0.val) := by sorry

end QAlgorithms.Papers.Independent.Frontier18.P01

end
