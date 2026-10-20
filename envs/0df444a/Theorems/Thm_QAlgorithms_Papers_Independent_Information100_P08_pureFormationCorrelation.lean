-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P08_pureFormationCorrelation
-- name    : QAlgorithms.Papers.Independent.Information100.P08.pureFormationCorrelation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T16:20:48.478982+00:00
-- url     : https://prove2.me/theorems/71de7d3b-7748-4f56-a31b-287b30f02ee4
-- title:
--   Appendix F.1: pure-state formation–correlation bound
-- statement:
--   All systems below have finite positive dimension. States are positive semidefinite matrices of trace one, channels are completely positive trace-preserving maps, and entropies are in bits. Write $S$ for von Neumann entropy and $E_F(A;B)$ for the pure convex roof of marginal entropy across the indicated cut. For a state $\sigma_{BE}$, $J(E;B)_\sigma$ is the supremum of outcome–$B$ mutual information over finite POVMs on $E$, and $G_E(\sigma)$ is its convex roof over decompositions into possibly mixed states. For every normalized pure state $\phi_{B_1B_2E_1E_2}$, $$S(B_1B_2)_\phi\ge E_F(B_1;E_1)_\phi+J(E_2;B_2)_{\phi_{B_2E_2}}.$$ The correlation optimizes measurements on $E_2$. No existence assumption for an optimizing POVM is required. This is the pure-state component of the formation marginal inequality.
-- source:
--   Entanglement -of-formation potentials for feedback-assisted classical communication and randomness distillation, arXiv:2610.04831v1, PDF p. 74, Appendix F.1: pure-state formation–correlation bound

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P08

namespace QAlgorithms.Papers.Independent.Information100.P08

open scoped Matrix ComplexConjugate ComplexOrder

noncomputable section

attribute [local instance] Classical.propDecidable

/-- PDF pp.73-74, (F.11): pure-state formation-correlation inequality, without assuming
an optimizing POVM exists. The measurement in J is on E2. -/
theorem pureFormationCorrelation {a b c d : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (phi : Matrix ((Fin a × Fin b) × (Fin c × Fin d))
      ((Fin a × Fin b) × (Fin c × Fin d)) ℂ) (hphi : IsPure phi) :
    formation (firstPair phi) + measuredCorrelation (secondPair phi) ≤ vnEntropy (traceRight phi) := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P08
