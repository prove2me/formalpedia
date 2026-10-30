-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P29_orthogonalizeKraus
-- name    : QAlgorithms.Papers.Independent.Advance50.P29.orthogonalizeKraus
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T22:11:48.167312+00:00
-- url     : https://prove2.me/theorems/a2812c39-277d-4b43-a2b0-2fbbff860f72
-- title:
--   §6 footnote 4: orthogonalization of a minimal Kraus representation
-- statement:
--   Let $Q$ and $Q^{\prime}$ be finite complex Hilbert spaces of positive dimensions $M$ and $D$. A density operator is positive semidefinite with trace one. All logarithms and entropies are in bits. Write $\pi=I_Q/M$. Let $(B_j)_{j\in L}$ be any minimal finite Kraus family for a CPTP map $\mathcal N:B(Q)\to B(Q^{\prime})$. There exists a unitary $U$ on $\mathbb C^L$ such that, on defining $A_m=\sum_{j\in L}(U^\dagger)_{jm}B_j$,
--
--   $$
--   \mathcal N(X)=\sum_{m\in L}A_mXA_m^\dagger\quad\text{for every }X,\qquad\operatorname{tr}(A_l^\dagger A_m)=0\quad(l\ne m).
--   $$
--
--   The new family remains minimal and covers rectangular input/output spaces. This fixes a diagonal representation before taking tensor powers.
-- source:
--   A random-coding based proof for the quantum coding theorem, arXiv:0712.2558v1, PDF p. 14, §6 footnote 4: orthogonalization of a minimal Kraus representation

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P29

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P29

open QAlgorithms MeasureTheory Filter

open QAlgorithms.Papers.Independent.Information100.P22
  (densityPurification coherentInformation singleUseInformation mixed)

open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

open QAlgorithms.Papers.Independent.Dependency50.P48 (wordProbability)

open QAlgorithms.Papers.Independent.Bridge50.P43 (tensorDensity)

open scoped Matrix ComplexConjugate ComplexOrder Topology

attribute [local instance] Classical.propDecidable

variable {I J E L : Type} [Fintype I] [DecidableEq I]

variable [Fintype J] [DecidableEq J] [Fintype E] [DecidableEq E]

variable [Fintype L] [DecidableEq L]

/-- PDF p.14, footnote 4, used p.16: unitary mixing diagonalizes a minimal rectangular
Kraus representation, retaining both its action and minimality. -/
theorem orthogonalizeKraus [Nonempty I] [Nonempty J]
    (B : L → Matrix J I ℂ) (hB : IsKrausFamily B) (hm : MinimalKraus B) :
    ∃ U : Matrix.unitaryGroup L ℂ,
      let A : L → Matrix J I ℂ := fun m => ∑ j, ((U : Matrix L L ℂ)ᴴ j m) • B j
      (∀ X, krausApply A X = krausApply B X) ∧ MinimalKraus A ∧
        ∀ l m, l ≠ m → ((A l)ᴴ * A m).trace = 0 := by sorry

end QAlgorithms.Papers.Independent.Advance50.P29

end
