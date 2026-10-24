-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P18_entropy_combination_LAA
-- name    : QAlgorithms.Papers.Independent.Support50.P18.entropy_combination_LAA
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T20:21:23.565993+00:00
-- url     : https://prove2.me/theorems/a4952bf0-796f-4dc5-8be4-0f6cfc6a8e81
-- title:
--   Section 5.1: LAA constants for linear combinations of marginal entropies
-- statement:
--   Consider finitely many separable quantum systems $A_1,\ldots,A_n$, selected subsystems $X_1,\ldots,X_m$, and real coefficients $c_k$. Set $f(\rho)=\sum_k c_kH(\rho_{X_k})$ on the real-valued domain where every marginal entropy with nonzero coefficient is finite. Put $a=\sum_k\max\{-c_k,0\}$ and $b=\sum_k\max\{c_k,0\}$. For states $\rho,\sigma$ in that domain and $0<p<1$, their mixture also belongs to the domain and
--
--   $$-a h_2(p)\le f(p\rho+(1-p)\sigma)-pf(\rho)-(1-p)f(\sigma)\le b h_2(p).$$
--
--   Thus these sums are valid LAA constants; the source allows smaller constants as well. The statement applies in finite dimension and on the specified finite-entropy domain in infinite dimension.
-- source:
--   Adaptation of the Alicki-Fannes-Winter method for the set of states with bounded energy and its use, arXiv:1609.07044v5, PDF p. 10, Section 5.1

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P18

noncomputable section

open Filter

open scoped ENNReal NNReal BigOperators Topology

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Support50.P18

open QAlgorithms.Papers.Independent.Dependency50.P33 (State PureState traceSize rankOne)

open QAlgorithms.Papers.Independent.Frontier18.P01 (convexOperatorMixture traceSecond)

open QAlgorithms.Papers.Independent.Frontier18.P07
  (extendedEntropyNats extendedRelativeEntropyNats)

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Claimed50.P39 (g)

open QAlgorithms.Papers.Independent.Renew46.P08
  (coefficientEnergy entropySupremum extendedHalfTraceDistance)

/-- Section 5.1, PDF pp.9--10: negative coefficients contribute to the lower
LAA defect and positive coefficients to the upper defect. Finiteness describes
the real combination's domain in the source's infinite-dimensional discussion.
The mixed marginal entropies are finite as a conclusion. Footnote 5 allows
smaller valid constants; the displayed sums themselves are valid constants. -/
theorem entropy_combination_LAA {n m : ℕ} {I : Fin n → Type}
    [∀ i, Countable (I i)] (S : Fin m → Finset (Fin n)) (c : Fin m → ℝ)
    (rho sigma : State ((i : Fin n) → I i))
    (hrho : ∀ k, c k ≠ 0 → extendedEntropyNats (subsystemMarginal (S k) rho.coefficients) < ⊤)
    (hsigma : ∀ k, c k ≠ 0 → extendedEntropyNats (subsystemMarginal (S k) sigma.coefficients) < ⊤)
    (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    (∀ k, c k ≠ 0 → extendedEntropyNats (subsystemMarginal (S k)
      (convexOperatorMixture p rho.coefficients sigma.coefficients)) < ⊤) ∧
    -(∑ k, max (-c k) 0) * Real.binEntropy p ≤
      entropyCombination S c (convexOperatorMixture p rho.coefficients sigma.coefficients) -
        p * entropyCombination S c rho.coefficients -
        (1 - p) * entropyCombination S c sigma.coefficients ∧
    entropyCombination S c (convexOperatorMixture p rho.coefficients sigma.coefficients) -
        p * entropyCombination S c rho.coefficients -
        (1 - p) * entropyCombination S c sigma.coefficients ≤
      (∑ k, max (c k) 0) * Real.binEntropy p := by sorry

end QAlgorithms.Papers.Independent.Support50.P18

end
