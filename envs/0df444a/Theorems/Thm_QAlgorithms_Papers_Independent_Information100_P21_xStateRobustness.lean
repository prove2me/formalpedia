-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P21_xStateRobustness
-- name    : QAlgorithms.Papers.Independent.Information100.P21.xStateRobustness
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:55:25.827993+00:00
-- url     : https://prove2.me/theorems/0b748919-ce3b-4ae7-9733-353947d8194d
-- title:
--   IV.15 — Theorem IV.15 (Two-qubit X-state robustness). If z 2 > ad, then
-- statement:
--   Let $\rho_X$ have diagonal entries $a,b,c,d$ and real nonnegative anti-diagonal coherences $w,z$, with nonnegative entries, trace one, $w^2\le ad$ and $z^2\le bc$. Then both robustnesses agree. In the $z$-entangled branch,
--   $$R=\begin{cases}(z^2-ad)/\max(a,d),&\sqrt{ad}<z\le\max(a,d),\\2z-a-d,&z>\max(a,d).\end{cases}$$
--   For $w^2>bc$ replace $(a,d,z)$ by $(b,c,w)$. If neither strict entanglement inequality holds, both values are zero. This covers all ranks, zero diagonals and both boundaries. Local phase rotations put complex X coherences into this canonical form.
-- source:
--   The Minimal Dimension of Entangled -Noise Advantage, arXiv:2609.28367v1, PDF p. 13, IV.15 — Theorem IV.15 (Two-qubit X-state robustness). If z 2 > ad, then

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P21

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Information100.P21

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arxiv:2609.28367v1, PDF p. 13, Theorem IV.15 (Two-qubit X-state robustness). If z 2 > ad, then. -/
theorem xStateRobustness (a b c d w z : ℝ) (h : physicalX a b c d w z) :
  rs (xstate a b c d w z)=rg (xstate a b c d w z) ∧
  (a*d<z^2 → rg (xstate a b c d w z)=branchValue a d z) ∧
  (b*c<w^2 → rg (xstate a b c d w z)=branchValue b c w) ∧
  (z^2≤a*d → w^2≤b*c → rg (xstate a b c d w z)=0) := by sorry

end QAlgorithms.Papers.Independent.Information100.P21

end
