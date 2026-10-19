-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P21_rankOneSubtraction
-- name    : QAlgorithms.Papers.Independent.Information100.P21.rankOneSubtraction
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:47:11.329983+00:00
-- url     : https://prove2.me/theorems/c6abfe81-e27b-4cbb-88b6-0ee98eb990ab
-- title:
--   II.3 — Lemma II.3 (Rank-one subtraction). Let W ⪰ 0, and let the normalized vector |p⟩ belong to ran W . Write the
-- statement:
--   Let $W\succeq0$ and let $p$ be a unit vector in its range. Let $W^+$ invert positive support eigenvalues and vanish on the kernel. Then $c=\langle p|W^+|p\rangle>0$, and
--   $$t_*=c^{-1}>0,\qquad W-t_*|p\rangle\langle p|\succeq0,\qquad \operatorname{rank}(W-t_*|p\rangle\langle p|)<\operatorname{rank}W.$$
--   This is the rank-reducing subtraction used in the standard dual.
-- source:
--   The Minimal Dimension of Entangled -Noise Advantage, arXiv:2609.28367v1, PDF p. 7, II.3 — Lemma II.3 (Rank-one subtraction). Let W ⪰ 0, and let the normalized vector |p⟩ belong to ran W . Write the

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P21

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Information100.P21

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arxiv:2609.28367v1, PDF p. 7, Lemma II.3 (Rank-one subtraction). Let W ⪰ 0, and let the normalized vector |p⟩ belong to ran W . Write the. -/
theorem rankOneSubtraction (W : Op QQ) (hW : W.PosSemidef) (p : Vec QQ) (hp : ‖p‖=1)
  (hr : (fun i => p i) ∈ LinearMap.range (Matrix.toLin' W)) :
  0 < quad (pseudo W) p ∧ 0 < (quad (pseudo W) p)⁻¹ ∧
    (W - ((quad (pseudo W) p)⁻¹:ℂ) • proj p).PosSemidef ∧
    Matrix.rank (W - ((quad (pseudo W) p)⁻¹:ℂ) • proj p) < Matrix.rank W := by sorry

end QAlgorithms.Papers.Independent.Information100.P21

end
