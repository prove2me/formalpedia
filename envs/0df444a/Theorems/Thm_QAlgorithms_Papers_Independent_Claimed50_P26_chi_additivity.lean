-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P26_chi_additivity
-- name    : QAlgorithms.Papers.Independent.Claimed50.P26.chi_additivity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T12:00:40.232572+00:00
-- url     : https://prove2.me/theorems/9f87210a-da7e-459f-8c1f-41dcb3c0b88e
-- title:
--   Theorem I.4 (Additivity of χ*α)
-- statement:
--   Let $\Phi$ be a channel between nonzero finite-dimensional spaces, covariant under continuous unitary representations of a compact group with irreducible output representation. At any order $\alpha>1$ for which minimum output Rényi entropy is additive under every positive tensor power, one has, for every positive integer $n$,
--
--   $$
--   \chi_\alpha^*(\Phi^{\otimes n})
--   =n\chi_\alpha^*(\Phi)
--   =n\bigl(\log_2d_{\rm out}-S_\alpha^{\min}(\Phi)\bigr).
--   $$
--
--   In particular, under assumption (B), some $\beta>1$ witnesses the minimum-output identities for all $1\le\alpha<\beta$ and the displayed Holevo identities for all $1<\alpha<\beta$. Here $d_{\rm out}$ is the output dimension and all entropies are in bits. This is the same-order additivity implication used in the strong converse; local assumption (B) does not imply an identity at every order above one.
-- source:
--   A strong converse for classical channel coding using entangled inputs, arXiv:0903.2838v1, PDF p. 6, Theorem I.4 (Additivity of χ*α)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P26

noncomputable section

open scoped Matrix ComplexOrder ComplexConjugate Topology

open Filter

namespace QAlgorithms.Papers.Independent.Claimed50.P26

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P08 (Ensemble ensembleAverage depolarizing)

open QAlgorithms.Papers.Independent.Information100.P71
  (supportPower channelPower)

open QAlgorithms.Papers.Independent.Dependency50.P23
  (UACode uaCodeSuccess uaSuccess ordinaryClassicalCapacity)

open QAlgorithms.Papers.Independent.Information100.P60 (wernerHolevo)

open QAlgorithms.Papers.Independent.Dependency50.P35 (renyiEntropy petz relative)

open QAlgorithms.Papers.Independent.Dependency50.P24 (cqState)

/-- PDF p.6, Theorem I.4, corrected order scope: the identity holds throughout
each order with pointwise self-additivity, hence throughout the neighborhood
where (B) supplies additivity. Local (B) gives no all-order conclusion. -/
theorem chi_additivity {I J : Type} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] [Nonempty I] [Nonempty J]
    (Phi : Superop I J) (hPhi : IsChannel Phi)
    (hA : CovariantIrreducible Phi) (hB : LocalEntropyAdditive Phi) :
    (∀ alpha : ℝ, 1 < alpha →
      (∀ k : ℕ, 0 < k → minOutput alpha (channelPower Phi k) =
        (k : ℝ)*minOutput alpha Phi) →
      ∀ n : ℕ, 0 < n →
        channelChi alpha (channelPower Phi n) = (n : ℝ)*channelChi alpha Phi ∧
        (n : ℝ)*channelChi alpha Phi =
          (n : ℝ)*(Real.logb 2 (Fintype.card J)-minOutput alpha Phi)) ∧
    ∃ beta : ℝ, 1 < beta ∧
      (∀ alpha : ℝ, 1 ≤ alpha → alpha < beta → ∀ n : ℕ, 0 < n →
        minOutput alpha (channelPower Phi n) = (n : ℝ)*minOutput alpha Phi) ∧
      ∀ alpha : ℝ, 1 < alpha → alpha < beta → ∀ n : ℕ, 0 < n →
        channelChi alpha (channelPower Phi n) = (n : ℝ)*channelChi alpha Phi ∧
        (n : ℝ)*channelChi alpha Phi =
          (n : ℝ)*(Real.logb 2 (Fintype.card J)-minOutput alpha Phi) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P26

end
