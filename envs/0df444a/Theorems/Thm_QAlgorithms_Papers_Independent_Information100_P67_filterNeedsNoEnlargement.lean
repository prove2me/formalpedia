-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P67_filterNeedsNoEnlargement
-- name    : QAlgorithms.Papers.Independent.Information100.P67.filterNeedsNoEnlargement
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T12:57:15.634805+00:00
-- url     : https://prove2.me/theorems/ec0b78e5-fbf0-453b-b692-fd8b1917a203
-- title:
--   Remark 5.2 (No enlargement is needed)
-- statement:
--   Under the hypotheses of Lemma 5.1, the filter, normalized filtered state, and CPTP recovery can satisfy all the same recovery and conditional-entropy dimension guarantees while also satisfying
--
--   $$1\le|C|\le|A|.$$
--
--   In particular the recovery error is at most $\delta$, the smoothing parameter is $\delta^2/16$, and the output dimension obeys exactly the positive-part bound of (5.3). This is a non-enlargement guarantee, with no assertion of strict dimension reduction for every input.
-- source:
--   An exponential strong converse for private communication over degradable quantum channels, arXiv:2609.32515v1, PDF p. 27, Remark 5.2 (No enlargement is needed)

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P67

noncomputable section

open scoped BigOperators ComplexConjugate Matrix ComplexOrder

open MeasureTheory Filter

namespace QAlgorithms.Papers.Independent.Information100.P67

variable {A B E R S T X C Y G1 G2 : Type*}

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype E] [DecidableEq E] [Fintype R] [DecidableEq R]

variable [Fintype S] [DecidableEq S] [Fintype T] [DecidableEq T]

variable [Fintype X] [DecidableEq X] [Fintype C] [DecidableEq C]

variable [Fintype Y] [DecidableEq Y] [Fintype G1] [DecidableEq G1]

variable [Fintype G2] [DecidableEq G2]

/-- Remark 5.2, PDF p.27: the same entropy and recovery guarantee with
no enlargement, rather than an unconditional strict dimension decrease. -/
theorem filterNeedsNoEnlargement [Nonempty A] [Nonempty B] [Nonempty R]
    (psi : EuclideanSpace ℂ ((A × B) × R)) (hpsi : IsState psi)
    (delta : ℝ) (hd0 : 0 < delta) (hd1 : delta < 1 / 2) :
    ∃ L : ℕ, 0 < L ∧ L ≤ Fintype.card A ∧ ∃ Z : Matrix (Fin L) A ℂ,
      ∃ rec : Superop (Fin L × B) (A × B), FilterGuarantee psi delta L Z rec := by sorry

end QAlgorithms.Papers.Independent.Information100.P67

end
