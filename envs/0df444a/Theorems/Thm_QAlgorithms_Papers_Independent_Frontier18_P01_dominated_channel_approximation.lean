-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P01_dominated_channel_approximation
-- name    : QAlgorithms.Papers.Independent.Frontier18.P01.dominated_channel_approximation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:44:59.000988+00:00
-- url     : https://prove2.me/theorems/2bf491e8-7967-4f7b-824c-d49aac7b3091
-- title:
--   Lemma 4: dominated inputs and output-channel approximation
-- statement:
--   All Hilbert spaces are complex and separable, with completed Hilbert tensor products. States are positive trace-class operators of trace one, and channels are completely positive and trace preserving. Write $H$ for entropy and $D$ for relative entropy, using natural logarithms; $I(\rho,\Phi)$ is the relative entropy of the channel-applied purification against the product of its marginals. Let $\Phi:A\to B$ be any channel and let channels $\Pi_n:B\to B$ converge strongly to the identity. Suppose $\rho_n\to\rho_0$ in trace norm and real numbers $\lambda_n\to1$ satisfy $\lambda_n\rho_n\le\rho_0$ in operator order for every $n$. Then
--
--   $$\lim_{n\to\infty}I(\rho_n,\Pi_n\circ\Phi)=I(\rho_0,\Phi).$$
--
--   No entropy finiteness or sign restriction on a finite prefix of $\lambda_n$ is required. This is the dominated-input approximation property.
-- source:
--   Mutual and coherent informations for infinite-dimensional quantum channels, arXiv:1004.2495v2, PDF p. 12, Lemma 4: dominated inputs and output-channel approximation

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P01

noncomputable section

open Filter

open scoped ENNReal

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Frontier18.P01

variable {I J K L E R : Type}

/-- Lemma 4, PDF p.12. Real lambda_n may have a negative finite prefix;
no positivity condition or entropy restriction is added. -/
theorem dominated_channel_approximation [Countable I] [Countable J] (Phi : Channel I J)
    (Pi : ℕ → Channel J J) (hPi : ∀ sigma : State J,
      Tendsto (fun n => traceSize ((Pi n).val sigma.coefficients - sigma.coefficients))
        atTop (nhds 0))
    (rho : ℕ → State I) (rho0 : State I) (hrho : Tendsto rho atTop (nhds rho0))
    (weight : ℕ → ℝ) (hw : Tendsto weight atTop (nhds 1))
    (hdom : ∀ n, TraceOperatorLE ((weight n : ℂ) • (rho n).coefficients) rho0.coefficients) :
    Tendsto (fun n => mutualInformation (rho n).coefficients ((Pi n).val ∘ Phi.val)) atTop
      (nhds (mutualInformation rho0.coefficients Phi.val)) := by sorry

end QAlgorithms.Papers.Independent.Frontier18.P01

end
