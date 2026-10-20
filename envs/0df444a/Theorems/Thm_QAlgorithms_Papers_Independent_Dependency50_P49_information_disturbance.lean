-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P49_information_disturbance
-- name    : QAlgorithms.Papers.Independent.Dependency50.P49.information_disturbance
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T18:19:41.599257+00:00
-- url     : https://prove2.me/theorems/e94b7803-96b6-4e36-bb64-fcb2c460742b
-- title:
--   Information–disturbance tradeoff with explicit depolarizing-state quantifiers
-- statement:
--   Let $T_B:\mathcal B(H_B)\to\mathcal B(H_A)$ be a completely positive unital complex-linear map between positive-dimensional finite complex systems. Let $V:H_A\to H_B\otimes H_E$ be any Stinespring isometry, with positive-dimensional finite $H_E$, and put $T_E(e)=V^*(I_B\otimes e)V$. For each density operator $\sigma$ on $H_E$, set $S_\sigma(e)=\operatorname{tr}(\sigma e)I_A$. Let $r=\inf_D\|T_BD-\operatorname{id}_A\|_{\rm cb}$, where $D:\mathcal B(H_A)\to\mathcal B(H_B)$ ranges over all completely positive unital decoding channels. Then
--
--   $$\forall\sigma:\quad\tfrac14r^2\leq\|T_E-S_\sigma\|_{\rm cb},\qquad \exists\sigma:\quad\|T_E-S_\sigma\|_{\rm cb}\leq 2\sqrt r.$$
--
--   In both quantifiers $\sigma$ ranges over normalized density operators. Thus some $S_\sigma$ satisfies the displayed chain in the paper. This relates optimal recovery to complementary privacy, using unhalved cb-norms.
-- source:
--   The Information-Disturbance Tradeoff and the Continuity of Stinespring's Representation, arXiv:quant-ph/0605009v1, PDF p. 9, Theorem 3, Eqs. (32)–(33)

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

/-- PDF p.9, Theorem 3, (32)–(33), read with the proof on pp.10–11:
the lower estimate holds for every depolarizing state; the upper estimate supplies
one, generally different, state. In particular that state satisfies the printed chain. -/
theorem information_disturbance {a b e : ℕ} (ha : 0 < a) (hb : 0 < b) (he : 0 < e)
    (T : MatrixMap (Fin b) (Fin a)) (hT : IsQuantumChannel T)
    (V : Matrix (Fin b × Fin e) (Fin a) ℂ) (hV : QAlgorithms.Papers.Independent.Information100.P71.IsStinespring (traceDual T) V) :
    (∀ sigma : Mat (Fin e), IsDensityMatrix sigma →
      (1 / 4 : ℝ) * optimalDecodingError T ^ 2 ≤ cbNorm (complement V - stateReplacement sigma)) ∧
    (∃ sigma : Mat (Fin e), IsDensityMatrix sigma ∧
      cbNorm (complement V - stateReplacement sigma) ≤ 2 * Real.sqrt (optimalDecodingError T)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P49

end
