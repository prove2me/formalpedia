-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P08_formationMarginal
-- name    : QAlgorithms.Papers.Independent.Information100.P08.formationMarginal
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T16:19:52.077121+00:00
-- url     : https://prove2.me/theorems/4a5c54df-7c29-450f-a58e-e71cabcf0a60
-- title:
--   Appendix F: formation marginal inequality
-- statement:
--   All systems below have finite positive dimension. States are positive semidefinite matrices of trace one, channels are completely positive trace-preserving maps, and entropies are in bits. Write $S$ for von Neumann entropy and $E_F(A;B)$ for the pure convex roof of marginal entropy across the indicated cut. For a state $\sigma_{BE}$, $J(E;B)_\sigma$ is the supremum of outcome–$B$ mutual information over finite POVMs on $E$, and $G_E(\sigma)$ is its convex roof over decompositions into possibly mixed states. For every four-partite state $\sigma_{B_1B_2E_1E_2}$, $$E_F(B_1B_2;E_1E_2)_\sigma\ge E_F(B_1;E_1)_\sigma+G_{E_2}(\sigma_{B_2E_2}).$$ No product or full-rank assumption is made. The second term is the mixed roof of correlation measured on $E_2$, not a second entanglement-of-formation term.
-- source:
--   Entanglement -of-formation potentials for feedback-assisted classical communication and randomness distillation, arXiv:2610.04831v1, PDF p. 73, Appendix F: formation marginal inequality

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P08

namespace QAlgorithms.Papers.Independent.Information100.P08

open scoped Matrix ComplexConjugate ComplexOrder

noncomputable section

attribute [local instance] Classical.propDecidable

/-- PDF pp.39,73-75, (F.1): arbitrary four-partite state, with G (not E_F) on the second pair. -/
theorem formationMarginal {a b c d : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (sigma : Matrix ((Fin a × Fin b) × (Fin c × Fin d))
      ((Fin a × Fin b) × (Fin c × Fin d)) ℂ) (hsigma : IsDensityMatrix sigma) :
    formation (firstPair sigma) + environmentRoof (secondPair sigma) ≤ formation sigma := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P08
