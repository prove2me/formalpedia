-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P46_local_divergence_cancellation
-- name    : QAlgorithms.Papers.Independent.Support50.P46.local_divergence_cancellation
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-23T23:59:12.104709+00:00
-- url     : https://prove2.me/theorems/c11a4483-df8e-4412-b7ea-78fbdf505ec7
-- title:
--   Local codimension-m divergences cancel in the alternating n-region sum
-- statement:
--   Let n,m,D be nonnegative integers with D>m and n>m+1. Index the n regions by {1,…,n}. Let J be the incident regions of a local codimension-m junction, with |J|≤m+1. At a fixed common cutoff let f be its real local entropy contribution as a function of the selected incident regions, with f(∅)=0. For a subset σ of all regions its contribution is f(σ∩J). With the coefficients printed in (6.2),
--
--   $$
--   \sum_{\sigma\subseteq\{1,\ldots,n\}}(-1)^{|\sigma|}f(\sigma\cap J)=0.
--   $$
--
--   Thus every local divergence of this prescribed form cancels. This does not assert that all divergences of an arbitrary field theory have this locality property. The printed alternating sign is the negative of the three-party convention in (1.5); cancellation is unchanged.
-- source:
--   Holographic Mutual Information is Monogamous, arXiv:1107.2940v2, PDF p. 19, §6.1: cancellation of local codimension-m divergences

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P46

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P46

open scoped BigOperators ComplexConjugate

open QAlgorithms.Papers.Independent.Gap48.P20 (subsystemEntropy)

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- PDF pp.18–19, (6.2): in D>m dimensions, a local codimension-m junction
involves at most m+1 regions. Its contribution cancels whenever n>m+1.
The local function is arbitrary, subject to the empty-entropy convention;
locality is implemented by intersection with the incident subset. -/
theorem local_divergence_cancellation (n m D : ℕ) (hD : m < D)
    (hn : m + 1 < n) (incident : Finset (Fin n))
    (hincident : incident.card ≤ m + 1) (f : Finset (Fin n) → ℝ)
    (hempty : f ∅ = 0) :
    alternatingInformation n (localDivergence incident f) = 0 := by sorry

end QAlgorithms.Papers.Independent.Support50.P46

end
