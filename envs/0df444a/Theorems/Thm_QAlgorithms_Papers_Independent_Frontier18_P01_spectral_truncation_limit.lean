-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P01_spectral_truncation_limit
-- name    : QAlgorithms.Papers.Independent.Frontier18.P01.spectral_truncation_limit
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:44:27.560568+00:00
-- url     : https://prove2.me/theorems/a8b4802e-733d-4716-bd9c-fce002c39cf4
-- title:
--   Lemma 3: normalized spectral truncations, finite-dimensional output
-- statement:
--   All Hilbert spaces are complex and separable, with completed Hilbert tensor products. States are positive trace-class operators of trace one, and channels are completely positive and trace preserving. Write $H$ for entropy and $D$ for relative entropy, using natural logarithms; $I(\rho,\Phi)$ is the relative entropy of the channel-applied purification against the product of its marginals. Let $\Phi:A\to B$ have finite-dimensional output. Choose a spectral presentation $\rho=\sum_{i\ge1}\lambda_i|e_i\rangle\langle e_i|$ with a positive first eigenvalue; zero-weight padding includes finite-rank inputs. For $n\ge1$ put $\mu_n=\sum_{i=1}^n\lambda_i$ and $\rho_n=\mu_n^{-1}\sum_{i=1}^n\lambda_i|e_i\rangle\langle e_i|$. Then
--
--   $$\lim_{n\to\infty}I(\rho_n,\Phi)=I(\rho,\Phi).$$
--
--   This includes infinite input entropy. The positive-mass enumeration is available for every state and only makes the normalization well defined.
-- source:
--   Mutual and coherent informations for infinite-dimensional quantum channels, arXiv:1004.2495v2, PDF p. 10, Lemma 3: normalized spectral truncations, finite-dimensional output

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P01

noncomputable section

open Filter

open scoped ENNReal

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Frontier18.P01

variable {I J K L E R : Type}

/-- Lemma 3, PDF pp.10–12. The output basis is finite; the input is unrestricted.
The n+1 indexing and a positive first eigenvalue avoid a zero-mass prefix. -/
theorem spectral_truncation_limit [Countable I] [Countable J] [Finite J] (rho : State I) (Phi : Channel I J)
    (s : SpectralPresentation rho) :
    Tendsto (fun n => mutualInformation (spectralTruncation s n) Phi.val) atTop
      (nhds (mutualInformation rho.coefficients Phi.val)) := by sorry

end QAlgorithms.Papers.Independent.Frontier18.P01

end
