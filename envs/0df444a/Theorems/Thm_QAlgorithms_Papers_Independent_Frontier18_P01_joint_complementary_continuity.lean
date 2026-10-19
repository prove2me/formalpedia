-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P01_joint_complementary_continuity
-- name    : QAlgorithms.Papers.Independent.Frontier18.P01.joint_complementary_continuity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:58:16.102978+00:00
-- url     : https://prove2.me/theorems/cbb85752-1648-4854-90ca-c6c02c129786
-- title:
--   Proposition 5: joint continuity along convergent complementary channels
-- statement:
--   All Hilbert spaces are complex and separable, with completed Hilbert tensor products. States are positive trace-class operators of trace one, and channels are completely positive and trace preserving. Write $H$ for entropy and $D$ for relative entropy, using natural logarithms; $I(\rho,\Phi)$ is the relative entropy of the channel-applied purification against the product of its marginals. Suppose channels $\Phi_n:A\to B$ converge strongly to $\Phi_0$, and there are channels $\widetilde\Phi_n:A\to E$ converging strongly to $\widetilde\Phi_0$ on a fixed environment. Assume each pair, including the limiting pair, is complementary. If $\rho_n\to\rho_0$ in trace norm, each input has finite entropy, and $H(\rho_n)\to H(\rho_0)<\infty$, then
--
--   $$I(\rho_n,\Phi_n)\to I(\rho_0,\Phi_0),\qquad I_c(\rho_n,\Phi_n)\to I_c(\rho_0,\Phi_0).$$
--
--   Strong convergence means pointwise trace-norm convergence on every state. No convergence of chosen dilation isometries is required.
-- source:
--   Mutual and coherent informations for infinite-dimensional quantum channels, arXiv:1004.2495v2, PDF p. 22, Proposition 5: joint continuity along convergent complementary channels

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P01

noncomputable section

open Filter

open scoped ENNReal

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Frontier18.P01

variable {I J K L E R : Type}

/-- Proposition 5, equation (31), PDF p.22. A convergent complementary sequence
on one fixed environment is an explicit hypothesis; isometries need not converge. -/
theorem joint_complementary_continuity [Countable I] [Countable J] [Countable E] (Phi : ℕ → Channel I J) (Phi0 : Channel I J)
    (Psi : ℕ → Channel I E) (Psi0 : Channel I E)
    (hPhi : ∀ rho : State I, Tendsto
      (fun n => traceSize ((Phi n).val rho.coefficients - Phi0.val rho.coefficients)) atTop (nhds 0))
    (hPsi : ∀ rho : State I, Tendsto
      (fun n => traceSize ((Psi n).val rho.coefficients - Psi0.val rho.coefficients)) atTop (nhds 0))
    (hcomp : ∀ n, Complementary (Phi n) (Psi n)) (hcomp0 : Complementary Phi0 Psi0)
    (rho : ℕ → State I) (rho0 : State I) (hrho : Tendsto rho atTop (nhds rho0))
    (hfinite : ∀ n, homogeneousEntropy (rho n).coefficients < ⊤) (hfinite0 : homogeneousEntropy rho0.coefficients < ⊤)
    (hentropy : Tendsto (fun n => homogeneousEntropy (rho n).coefficients) atTop
      (nhds (homogeneousEntropy rho0.coefficients))) :
    Tendsto (fun n => mutualInformation (rho n).coefficients (Phi n).val) atTop
      (nhds (mutualInformation rho0.coefficients Phi0.val)) ∧
    Tendsto (fun n => finiteInputCoherentInfo (rho n).coefficients (Phi n).val) atTop
      (nhds (finiteInputCoherentInfo rho0.coefficients Phi0.val)) := by sorry

end QAlgorithms.Papers.Independent.Frontier18.P01

end
