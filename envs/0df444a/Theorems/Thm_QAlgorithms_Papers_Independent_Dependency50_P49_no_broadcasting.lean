-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P49_no_broadcasting
-- name    : QAlgorithms.Papers.Independent.Dependency50.P49.no_broadcasting
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T18:20:28.609502+00:00
-- url     : https://prove2.me/theorems/945603e8-e6c3-4d4d-8716-fdfce683d009
-- title:
--   Approximate no broadcasting
-- statement:
--   Identify $H,H_1,H_2$ with the same positive-dimensional finite complex Hilbert space, as in the source. Let $H_E$ be a positive-dimensional finite environment and let $V:H\to H_1\otimes H_2\otimes H_E$ be any isometry. Its local Heisenberg channels are $T_1(a)=V^*(a\otimes I_2\otimes I_E)V$ and $T_2(a)=V^*(I_1\otimes a\otimes I_E)V$. There exists a density operator $\sigma$ on $H_2$ such that, with $S_\sigma(a)=\operatorname{tr}(\sigma a)I_H$,
--
--   $$\|T_2-S_\sigma\|_{\rm cb}\leq2\sqrt{\|T_1-\operatorname{id}_H\|_{\rm cb}}.$$
--
--   The cb-norms carry no factor of one half. This bounds the second output's information when the first output is close to noiseless transmission.
-- source:
--   The Information-Disturbance Tradeoff and the Continuity of Stinespring's Representation, arXiv:quant-ph/0605009v1, PDF p. 12, Corollary 4, Eq. (43)

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

/-- PDF p.12, Corollary 4, (43): all three system spaces are identified with C^a.
V may have a nonminimal environment; neither marginal is assumed to broadcast. -/
theorem no_broadcasting {a e : ℕ} (ha : 0 < a) (he : 0 < e)
    (V : Matrix ((Fin a × Fin a) × Fin e) (Fin a) ℂ) (hV : Vᴴ * V = 1) :
    ∃ sigma : Mat (Fin a), IsDensityMatrix sigma ∧
      cbNorm (broadcastSecond V - stateReplacement sigma) ≤
        2 * Real.sqrt (cbNorm (broadcastFirst V - LinearMap.id)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P49

end
