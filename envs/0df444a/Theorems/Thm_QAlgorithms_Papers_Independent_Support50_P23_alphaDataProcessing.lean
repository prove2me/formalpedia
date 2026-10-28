-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P23_alphaDataProcessing
-- name    : QAlgorithms.Papers.Independent.Support50.P23.alphaDataProcessing
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-23T20:59:09.204112+00:00
-- url     : https://prove2.me/theorems/42d9ca33-c224-4383-8c22-84766f10d0ce
-- title:
--   Data processing on the conditioning system
-- statement:
--   Let $\rho_{AB}$ and $\sigma_B$ be normalized finite-dimensional states and $\mathcal E:B\to C$ a trace-preserving completely positive map. Put $\tau_{AC}=(\mathrm{id}_A\otimes\mathcal E)(\rho_{AB})$ and $\omega_C=\mathcal E(\sigma_B)$. For every $\alpha\in[0,2]$,
--   $$
--   H_\alpha(A|B)_{\rho|\sigma}\le H_\alpha(A|C)_{\tau|\omega}.
--   $$
--   The channel acts on arbitrary entangled inputs through its blockwise identity extension. Thus processing the side information cannot decrease this conditional entropy.
-- source:
--   A Fully Quantum Asymptotic Equipartition Property, arXiv:0811.1221v3, PDF p. 4, Lemma 5: data processing on conditioning system

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

/-- Lemma 5, PDF p.4, (20): processing B cannot decrease entropy; includes 0,1,2. -/
theorem alphaDataProcessing [Nonempty A] [Nonempty B] [Nonempty C]
    (rho : Matrix (A × B) (A × B) ℂ) (sigma : Matrix B B ℂ)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (E : Superop B C) (hE : IsChannel E) (alpha : ℝ≥0∞) (halpha : alpha ≤ 2) :
    alphaEntropy rho sigma alpha ≤
      alphaEntropy (idTensorSuperop (R := A) E rho) (E sigma) alpha := by sorry

end QAlgorithms.Papers.Independent.Support50.P23

end
