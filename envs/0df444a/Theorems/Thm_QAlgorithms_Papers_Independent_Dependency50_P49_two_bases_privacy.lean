-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P49_two_bases_privacy
-- name    : QAlgorithms.Papers.Independent.Dependency50.P49.two_bases_privacy
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T18:23:49.257994+00:00
-- url     : https://prove2.me/theorems/7e6d98d6-0c2c-4aef-9860-5362fc26b1f5
-- title:
--   Privacy on a half-dimensional code from two conjugate ensembles
-- statement:
--   Let $T_B:\mathcal B(\mathbb C^n)\to\mathcal B(\mathbb C^n)$ be a Heisenberg quantum channel, $n>0$, with any finite positive-dimensional Stinespring environment and complementary channel $T_E$. For $\epsilon>0$, suppose the uniform computational-basis ensemble and its Fourier-rotated ensemble each have output Holevo information at least $\log_2 n-\epsilon$. Holevo information means the entropy of the average output state minus the average output entropy, using the Schrödinger dual and entropy in bits. Then there are a positive integer $k$, an isometric code embedding $J:\mathbb C^k\to\mathbb C^n$, a decoding channel $D:\mathcal B(\mathbb C^k)\to\mathcal B(\mathbb C^n)$, and a density operator $\sigma$ on the original environment such that
--
--   $$k\geq n/2,\qquad \|T_B^{J}D-\operatorname{id}_k\|_{\rm cb}\leq13\epsilon^{1/8},\qquad\|T_E^{J}-S_\sigma\|_{\rm cb}\leq8\epsilon^{1/16}.$$
--
--   Here $T^{J}(X)=J^*T(X)J$ and $S_\sigma(e)=\operatorname{tr}(\sigma e)I_k$. This obtains stabilized privacy at the expense of halving the code dimension.
-- source:
--   The Information-Disturbance Tradeoff and the Continuity of Stinespring's Representation, arXiv:quant-ph/0605009v1, PDF p. 15, §VI, Eqs. (56)–(58) and following paragraph

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P49

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Kronecker Topology ENNReal

open Filter

open QAlgorithms.Papers.Independent.Information100.P75 (Mat)

open QAlgorithms.Papers.Independent.Information100.P30 (MatrixMap)

open QAlgorithms.Papers.Independent.Information100.P50 (coefficientMap)

open QAlgorithms.Papers.Independent.Information100.P08 (maximallyMixed)

namespace QAlgorithms.Papers.Independent.Dependency50.P49

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

-- The accepted all-Schatten norms at p=top are exactly the source's operator norms.

local notation "inducedNorm" => QAlgorithms.Papers.Independent.Information100.P50.inducedNorm (⊤ : ℝ≥0∞)

local notation "cbNorm" => QAlgorithms.Papers.Independent.Information100.P50.cbNorm (⊤ : ℝ≥0∞)

/-- PDF pp.14–15, (56)–(58) and following paragraph: the two Holevo hypotheses
produce a code of at least half the input dimension, a decoder with error
13 epsilon^(1/8), and complementary privacy 8 epsilon^(1/16).
All code restrictions are Heisenberg compressions by the same isometry J. -/
theorem two_bases_privacy {n e : ℕ} (hn : 0 < n) (he : 0 < e)
    (T : MatrixMap (Fin n) (Fin n)) (hT : IsQuantumChannel T)
    (V : Matrix (Fin n × Fin e) (Fin n) ℂ) (hV : QAlgorithms.Papers.Independent.Information100.P71.IsStinespring (traceDual T) V)
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hBasis : Real.logb 2 n - epsilon ≤ basisOutputHolevo T 1)
    (hFourier : Real.logb 2 n - epsilon ≤ basisOutputHolevo T (qftMatrix n)) :
    ∃ (k : ℕ), 0 < k ∧ n ≤ 2 * k ∧
      ∃ J : Matrix (Fin n) (Fin k) ℂ, Jᴴ * J = 1 ∧
      ∃ D : MatrixMap (Fin k) (Fin n), IsQuantumChannel D ∧
        cbNorm (((compression J).comp T).comp D - LinearMap.id) ≤
          13 * Real.rpow epsilon (1 / 8 : ℝ) ∧
        ∃ sigma : Mat (Fin e), IsDensityMatrix sigma ∧
          cbNorm ((compression J).comp (complement V) - stateReplacement sigma) ≤
            8 * Real.rpow epsilon (1 / 16 : ℝ) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P49

end
