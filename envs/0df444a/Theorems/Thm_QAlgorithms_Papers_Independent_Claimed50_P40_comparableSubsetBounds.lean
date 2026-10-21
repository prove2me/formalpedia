-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P40_comparableSubsetBounds
-- name    : QAlgorithms.Papers.Independent.Claimed50.P40.comparableSubsetBounds
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T10:52:28.241428+00:00
-- url     : https://prove2.me/theorems/1f54d16d-4ddd-465f-8baa-3ce492974153
-- title:
--   A saturated subset and comparable inequalities imply all inequalities
-- statement:
--   Fix the independent-input channel state $\gamma$ of a finite-dimensional classical-input multiple-access channel with $s\ge1$ finite nonempty sender alphabets. For $J\subseteq[s]$, write $R(J)=\sum_{i\in J}R_i$ and $f(J)=I_\gamma(X(J):YX(J^c))$.
--
--   Let $R_i\ge0$ and choose a nonempty $K\subseteq[s]$. Suppose only that
--   $$
--   R(K)=f(K),\qquad R(J)\le f(J)\ \text{whenever }J\subseteq K\text{ or }K\subseteq J.
--   $$
--   Then
--   $$
--   R(J)\le f(J)\qquad\text{for every }J\subseteq[s].
--   $$
--   Subset inclusion is inclusive, so $K=[s]$ is permitted. The information function is computed from the fixed product-input channel state, rather than replaced with an arbitrary set function. This reduces checking rate inequalities on a saturated face to checking comparable subsets.
-- source:
--   The Capacity of the Quantum Multiple Access Channel, arXiv:quant-ph/9807019v3, PDF p. 7, Lemma 11

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P40

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Claimed50.P40

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Lemma 11, PDF p.7: saturation at a nonempty K plus ONLY the comparable-subset
bounds implies every bound. Subset inclusion is inclusive, including K=[s]. -/
theorem comparableSubsetBounds {s : ℕ} (C : ClassicalChannel s)
    (P : InputLaw C.alphabet) (R : Fin s → ℝ) (hR : ∀ i, 0 ≤ R i)
    (K : Finset (Fin s)) (hK : K.Nonempty)
    (hsaturated : ∑ i ∈ K, R i = senderOutputMutualInformation C.state P K Kᶜ)
    (hbelow : ∀ J : Finset (Fin s), J ⊆ K →
      ∑ i ∈ J, R i ≤ senderOutputMutualInformation C.state P J Jᶜ)
    (habove : ∀ J : Finset (Fin s), K ⊆ J →
      ∑ i ∈ J, R i ≤ senderOutputMutualInformation C.state P J Jᶜ) :
    ∀ J : Finset (Fin s), ∑ i ∈ J, R i ≤ senderOutputMutualInformation C.state P J Jᶜ := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P40

end
