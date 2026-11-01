-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P63_accessible_concavity_affinity_minimax
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P63.accessible_concavity_affinity_minimax
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:15:04.200054+00:00
-- url     : https://prove2.me/theorems/90b42cdf-29fa-4657-9d2f-9d5d1036a921
-- title:
--   Concavity, tagged measurement affinity, and minimax
-- statement:
--   Fix normalized states $(\rho_i)_{i\in I}$ on a nonzero finite-dimensional space $E$, with a finite nonempty label set $I$. For a prior $p$ and finite POVM $Q$, let $\eta(p,Q)=H(I|J)$ for the law $p_i\operatorname{Tr}(\rho_iQ_j)$. Let $p^{(0)},p^{(1)}$ be probability vectors, let $0\le\lambda\le1$, and let $Q^{(0)},Q^{(1)}$ be POVMs. Their tagged mixture has disjoint outcome sets and effects $\lambda Q_j^{(0)}$ and $(1-\lambda)Q_k^{(1)}$. Then
--
--   $$\eta(\lambda p^{(0)}+(1-\lambda)p^{(1)},Q^{(0)})\ge\lambda\eta(p^{(0)},Q^{(0)})+(1-\lambda)\eta(p^{(1)},Q^{(0)}),$$
--   $$\eta(p^{(0)},\lambda Q^{(0)}\oplus(1-\lambda)Q^{(1)})=\lambda\eta(p^{(0)},Q^{(0)})+(1-\lambda)\eta(p^{(0)},Q^{(1)}),$$
--   $$\max_p S_{\rm acc}(p;\rho)=\max_p\min_Q\eta(p,Q)=\min_Q\max_p\eta(p,Q).$$
--
--   The extrema are attained, including the inner minimum for each prior. Entropies are in bits, with zero-probability terms contributing zero. Retaining the random branch tag is essential to the affinity assertion.
-- source:
--   Weak locking capacity of quantum channels can be much larger than private capacity, arXiv:1403.6361v3, PDF p. 8, Lemma 5: concavity, tagged-measurement affinity, and minimax

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P63

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P63

open QAlgorithms Filter

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)

open QAlgorithms.Papers.Independent.Information100.P04 (Measurement)

open QAlgorithms.Papers.Independent.Information100.P27 (shannon labelInformation)

open QAlgorithms.Papers.Independent.Information100.P71 (channelPower dilationMap SupportIncluded)

open QAlgorithms.Papers.Independent.Bridge50.P47 (SymmetricIndex universalSymmetricDilation)

open QAlgorithms.Learning (IsDistribution)

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.8, Lemma 5: concavity in priors, tagged-measurement affinity, and minimax.
The displayed max/min are attained; they are not replaced by unattained bounds. -/
theorem accessible_concavity_affinity_minimax {I E J K : Type}
    [Fintype I] [Nonempty I] [Fintype E] [DecidableEq E] [Nonempty E]
    [Fintype J] [Fintype K]
    (rho : I → Mat E) (hrho : ∀ i, IsDensityMatrix (rho i))
    (p0 p1 : I → ℝ) (hp0 : IsDistribution p0) (hp1 : IsDistribution p1)
    (Q : J → Mat E) (R : K → Mat E) (hQ : IsPOVM Q) (hR : IsPOVM R)
    (lambda : ℝ) (hl0 : 0 ≤ lambda) (hl1 : lambda ≤ 1) :
    (lambda * ensembleConditionalBits p0 rho Q + (1 - lambda) * ensembleConditionalBits p1 rho Q ≤
      ensembleConditionalBits (fun i => lambda * p0 i + (1 - lambda) * p1 i) rho Q) ∧
    (ensembleConditionalBits p0 rho (taggedEffects lambda Q R) =
      lambda * ensembleConditionalBits p0 rho Q + (1 - lambda) * ensembleConditionalBits p0 rho R) ∧
    (optimizedEquivocation rho = sInf {h | ∃ M : Measurement E, h = measurementWorstPrior rho M}) ∧
    (∃ p : I → ℝ, IsDistribution p ∧ accessibleEquivocation p rho = optimizedEquivocation rho) ∧
    (∀ p : I → ℝ, IsDistribution p → ∃ M : Measurement E,
      ensembleConditionalBits p rho M.effect = accessibleEquivocation p rho) ∧
    (∃ M : Measurement E, measurementWorstPrior rho M = optimizedEquivocation rho) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P63

end
