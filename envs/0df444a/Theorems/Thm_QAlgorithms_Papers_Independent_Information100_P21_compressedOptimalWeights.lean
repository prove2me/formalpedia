-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P21_compressedOptimalWeights
-- name    : QAlgorithms.Papers.Independent.Information100.P21.compressedOptimalWeights
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T10:07:51.479867+00:00
-- url     : https://prove2.me/theorems/bb22ec43-3d3c-4221-9453-abf49cbbbdf4
-- title:
--   VI — explicit optimal compressed weights
-- statement:
--   For a physical X state in the entangled $w$ branch, put $t=w>\sqrt{bc}$. Representative optimal weights are
--   $$(u_*,v_*)=\begin{cases}(t-b,t-c),&t\ge\max(b,c),\\(0,t^2/b-c),&b>t,\\(t^2/c-b,0),&c>t.\end{cases}$$
--   Both robustnesses equal $u_*+v_*>0$. The noise proportional to $u_*|01\rangle\langle01|+v_*|10\rangle\langle10|$ is normalized, separable and optimal. The $z$ branch uses $(a,d,z)$ and the even product pair. The internal equality boundary belongs to the first case. This gives a representative, not uniqueness.
-- source:
--   The Minimal Dimension of Entangled -Noise Advantage, arXiv:2609.28367v1, PDF p. 20, VI — explicit optimal compressed weights

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P21

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Information100.P21

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arxiv:2609.28367v1, PDF p. 20, explicit optimal compressed weights. -/
theorem compressedOptimalWeights (a b c d w z : ℝ) (h : physicalX a b c d w z) :
  ∀ odd : Bool, (if odd then b*c<w^2 else a*d<z^2) →
    let uv := if odd then weights b c w else weights a d z
    let Y := compressed odd uv.1 uv.2
    0≤uv.1 ∧ 0≤uv.2 ∧ 0<uv.1+uv.2 ∧ optG (xstate a b c d w z) Y ∧
    optS (xstate a b c d w z) Y ∧ rs (xstate a b c d w z)=uv.1+uv.2 ∧
    sep (((uv.1+uv.2)⁻¹:ℂ) • Y) ∧ QAlgorithms.IsDensityMatrix (((uv.1+uv.2)⁻¹:ℂ) • Y) ∧
    sep (mix (xstate a b c d w z) (((uv.1+uv.2)⁻¹:ℂ) • Y) (uv.1+uv.2)) := by sorry

end QAlgorithms.Papers.Independent.Information100.P21

end
