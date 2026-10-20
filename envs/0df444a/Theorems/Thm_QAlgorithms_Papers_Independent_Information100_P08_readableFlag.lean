-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P08_readableFlag
-- name    : QAlgorithms.Papers.Independent.Information100.P08.readableFlag
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T16:09:32.545029+00:00
-- url     : https://prove2.me/theorems/2be63859-4761-4a39-8062-485220d57447
-- title:
--   Readable-flag formation identity
-- statement:
--   All systems below have finite positive dimension. States are positive semidefinite matrices of trace one, channels are completely positive trace-preserving maps, and entropies are in bits. Write $S$ for von Neumann entropy and $E_F(A;B)$ for the pure convex roof of marginal entropy across the indicated cut. Let $(q_y,\rho^y_{AB})_y$ be any finite probability ensemble of states, and give Bob a readable orthonormal flag $Y$. For $\sigma_{ABY}=\sum_yq_y\rho^y_{AB}\otimes\lvert y\rangle\langle y\rvert$, $$E_F(A;BY)_\sigma=\sum_yq_yE_F(A;B)_{\rho^y}.$$ This is an exact flag identity, including zero weights.
-- source:
--   Entanglement -of-formation potentials for feedback-assisted classical communication and randomness distillation, arXiv:2610.04831v1, PDF p. 10, Readable-flag formation identity

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P08

namespace QAlgorithms.Papers.Independent.Information100.P08

open scoped Matrix ComplexConjugate ComplexOrder

noncomputable section

attribute [local instance] Classical.propDecidable

/-- PDF p.10, (2.16): an actually readable Bob flag gives exact average formation. -/
theorem readableFlag {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (e : Ensemble (Fin a × Fin b)) :
    formation (flaggedState e) = ∑ x, e.prob x * formation (e.state x) := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P08
