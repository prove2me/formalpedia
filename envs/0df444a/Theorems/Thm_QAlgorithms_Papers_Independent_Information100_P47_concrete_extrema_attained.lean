-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P47_concrete_extrema_attained
-- name    : QAlgorithms.Papers.Independent.Information100.P47.concrete_extrema_attained
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T11:37:50.627643+00:00
-- url     : https://prove2.me/theorems/4d3a3d04-4de3-403a-af36-da0b83aff4e0
-- title:
--   Attainment for the concrete continuous measurement distances
-- statement:
--   Let $A$ be an $n$-outcome POVM on $\mathbb C^d$, with $d,n\ge1$, and fix the computational basis. Let $D$ be one of the spectral distance $\frac12\sum_x\|A_x-B_x\|_{\mathrm{op}}$, the state-induced maximal total variation distance, or the measurement-channel diamond distance with factor $1/2$. Define coherence, sharpness, and maximal coherence by their infimum/supremum values. There exist a complete diagonal POVM $B$, a probability vector $q$, and a unitary $U$ such that
--
--   $$C_D(A)=D(A,B),\qquad S_D(A)=D(A,(q_xI)_x),\qquad C_D^{\max}(A)=C_D(U^\dagger A U).$$
--
--   For these concrete distances, the values used in the paper are exact minima and maxima. This supporting obligation avoids imposing attainment as an additional assumption on any main result.
-- source:
--   Maximal coherence of quantum measurement and the resource theory of sharpness, arXiv:2607.05847v1, PDF p. 4, Eqs. (4), (13), (15); concrete distances in Eqs. (5), (7), (32)

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P47

noncomputable section

open scoped BigOperators ComplexConjugate ENNReal Matrix

namespace QAlgorithms.Papers.Independent.Information100.P47

/-- PDF pp.2–4, Eqs.(4),(13),(15), specialized to the concrete continuous distances
used on pp.5–8: the infimum/supremum values are attained. This supplies the exact
minimum/maximum semantics, without adding attainment as a theorem hypothesis. -/
theorem concrete_extrema_attained (D : Distance)
    (hD : D = spectralDistance ∨ D = inducedDistance totalVariation ∨ D = diamondDistance)
    {d n : ℕ} (hd : 0 < d) (hn : 0 < n) (A : Measurement d n) (hA : IsPOVM A) :
    (∃ B : Measurement d n, IsPOVM B ∧ IsIncoherent B ∧ coherence D A = D d n A B) ∧
    (∃ q : Probability n, sharpness D A = D d n A (trivial q.val)) ∧
    (∃ U : Mat d, IsUnitary U ∧ maxCoherence D A = coherence D (rotate U A)) := by sorry

end QAlgorithms.Papers.Independent.Information100.P47

end
