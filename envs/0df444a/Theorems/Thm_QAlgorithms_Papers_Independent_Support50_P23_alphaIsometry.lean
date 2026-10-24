-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P23_alphaIsometry
-- name    : QAlgorithms.Papers.Independent.Support50.P23.alphaIsometry
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T20:58:17.878983+00:00
-- url     : https://prove2.me/theorems/d546091c-4b2a-4925-a582-c230420b71c9
-- title:
--   Local isometric invariance of fixed-reference alpha entropy
-- statement:
--   Let $\rho_{AB}$ and $\sigma_B$ be normalized states on finite-dimensional nonzero complex systems, and let $U:A\to C$ and $V:B\to D$ be isometries. Define $\tau_{CD}=(U\otimes V)\rho_{AB}(U\otimes V)^\dagger$ and $\omega_D=V\sigma_BV^\dagger$. For every $\alpha\in[0,\infty]$,
--   $$
--   H_\alpha(A|B)_{\rho|\sigma}=H_\alpha(C|D)_{\tau|\omega}.
--   $$
--   The output states are constructed from the input data. The equality expresses independence from the ambient local representation.
-- source:
--   A Fully Quantum Asymptotic Equipartition Property, arXiv:0811.1221v3, PDF p. 4, Lemma 4: local isometric invariance of alpha entropies

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P23

noncomputable section

open Filter

open scoped ENNReal ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Support50.P23

attribute [local instance] Classical.propDecidable

-- Exact accepted bodies. Other similarly named catalogue entries use different
-- smoothing, conditioning order, logarithm base, or channel-level objects.

open QAlgorithms.Papers.Independent.Gap20.P03 (fixedMin)

open QAlgorithms.Papers.Independent.Dependency50.P36 (relativeEntropy)

open QAlgorithms.Papers.Independent.Information100.P67 (IsSubnormalized)

open QAlgorithms.Papers.Independent.Information100.P69 (matrixPower)

variable {A B C D I : Type*}

variable [Fintype A] [Fintype B] [Fintype C] [Fintype D] [Fintype I]

variable [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D] [DecidableEq I]

/-- Lemma 4, PDF p.4, (19): output states are the specified local isometric images. -/
theorem alphaIsometry [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty D]
    (rho : Matrix (A × B) (A × B) ℂ) (sigma : Matrix B B ℂ)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (U : Matrix C A ℂ) (V : Matrix D B ℂ)
    (hU : U.conjTranspose * U = 1) (hV : V.conjTranspose * V = 1) (alpha : ℝ≥0∞) :
    alphaEntropy rho sigma alpha =
      alphaEntropy (Matrix.kronecker U V * rho * (Matrix.kronecker U V).conjTranspose)
        (V * sigma * V.conjTranspose) alpha := by sorry

end QAlgorithms.Papers.Independent.Support50.P23

end
