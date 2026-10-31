-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P50_maxConditionalInformation_attained
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P50.maxConditionalInformation_attained
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T23:50:05.344509+00:00
-- url     : https://prove2.me/theorems/066cc564-0a94-4f74-b9e0-5341e721752d
-- title:
--   Attainment of the one-use conditional-information maximum
-- statement:
--   Let $\Lambda$ be a finite-dimensional CPTP channel with positive input and output dimensions. There is a finite normalized ensemble of density operators on its input and a finite quantum auxiliary register for which the output conditional mutual information attains the supremum $J(\Lambda)$ used in Lemma 1 and Theorem 2. The auxiliary dimension, alphabet, probabilities, and conditional densities are all chosen as part of this ensemble. Entropy is measured in bits. Thus $J(\Lambda)$ is an actual maximum, as in the source.
-- source:
--   Quantum Feedback Channels, arXiv:quant-ph/0209076v4, PDF p. 2, §III.A, Lemma 1, Eq. (7); Theorem 2, Eq. (13)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P50

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P50

open QAlgorithms

/-- Bowen PDF p.2, Lemma 1, Eq. (7), and p.3, Theorem 2, Eq. (13):
the one-use conditional-information maximum is attained by a finite normalized
input–auxiliary ensemble. This supplies the maximum, not only its supremal value. -/
theorem maxConditionalInformation_attained {i o : ℕ}
    (hi : 0 < i) (ho : 0 < o) (N : Superop (Fin i) (Fin o)) (hN : IsChannel N) :
    ∃ E : BowenInputEnsemble i,
      maxConditionalInformation N = (bowenConditionalInformation N E : EReal) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P50

end
