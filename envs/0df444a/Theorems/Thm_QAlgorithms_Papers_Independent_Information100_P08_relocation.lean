-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P08_relocation
-- name    : QAlgorithms.Papers.Independent.Information100.P08.relocation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T15:58:37.146561+00:00
-- url     : https://prove2.me/theorems/c53e1326-f39e-451e-b345-0fb2e0257723
-- title:
--   Lemma 4.1: relocation inequality
-- statement:
--   All systems below have finite positive dimension. States are positive semidefinite matrices of trace one, channels are completely positive trace-preserving maps, and entropies are in bits. Write $S$ for von Neumann entropy and $E_F(A;B)$ for the pure convex roof of marginal entropy across the indicated cut. For every state $\sigma_{A^{\prime}B^{\prime}B}$, $$E_F(A^{\prime};B^{\prime}B)_\sigma\le E_F(A^{\prime}B^{\prime};B)_\sigma+S(B^{\prime}B)_\sigma-S(B)_\sigma.$$ Both cuts are taken on the same state. The conditional-entropy correction may be negative; no purity or product-state assumption is imposed.
-- source:
--   Entanglement -of-formation potentials for feedback-assisted classical communication and randomness distillation, arXiv:2610.04831v1, PDF p. 15, Lemma 4.1: relocation inequality

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P08

namespace QAlgorithms.Papers.Independent.Information100.P08

open scoped Matrix ComplexConjugate ComplexOrder

noncomputable section

attribute [local instance] Classical.propDecidable

/-- PDF pp.15-16, Lemma 4.1: the same state at two cuts; conditional entropy may be negative. -/
theorem relocation {a c b : ℕ} (ha : 0 < a) (hc : 0 < c) (hb : 0 < b)
    (sigma : Matrix (Fin a × (Fin c × Fin b)) (Fin a × (Fin c × Fin b)) ℂ)
    (hsigma : IsDensityMatrix sigma) :
    formation sigma ≤ formation (relocationCut sigma) +
      vnEntropy (traceLeft sigma) - vnEntropy (traceLeft (traceLeft sigma)) := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P08
