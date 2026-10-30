-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P25_mixture_entanglement
-- name    : QAlgorithms.Papers.Independent.Bridge50.P25.mixture_entanglement
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T18:07:55.697575+00:00
-- url     : https://prove2.me/theorems/31312ef2-106c-4d19-aae9-cfaf2a46d390
-- title:
--   Lemma V.1: mixture bound for state Emax
-- statement:
--   Let $\rho_1,\ldots,\rho_k$ be density matrices on a positive finite-dimensional bipartite system $A:B$. Let $p_i\in[0,1]$ satisfy $\sum_i p_i=1$, and set $\rho=\sum_i p_i\rho_i$. Then
--
--   $$\sum_i p_iE_{\max}^{A:B}(\rho_i)\le E_{\max}^{A:B}(\rho)+\sum_i p_iD_{\max}(\rho_i\|\rho).$$
--
--   The state entanglement is the minimum max-relative divergence to separable density matrices, with logarithms in bits. Zero weights are allowed and contribute zero even when their divergence is infinite. The sum-one hypothesis excludes an empty family.
--
--   This compares the mean entanglement of mixture components to the mixture and its component divergences.
-- source:
--   Relative Entropy Bounds on Quantum, Private and Repeater Capacities, arXiv:1604.03448v2, PDF p. 15, Lemma V.1

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P25

noncomputable section

namespace QAlgorithms.Papers.Independent.Bridge50.P25

open QAlgorithms QAlgorithms.Entanglement Filter

open scoped Matrix ComplexConjugate ComplexOrder BigOperators

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)

open QAlgorithms.Papers.Independent.Information100.P71 (channelPower)

open QAlgorithms.Papers.Independent.Dependency50.P35 (maxRelative)

open QAlgorithms.Papers.Independent.Support50.P21 (eMax)

variable {I J A B C D : Type}

variable [Fintype I] [DecidableEq I] [Nonempty I]

variable [Fintype J] [DecidableEq J] [Nonempty J]

variable [Fintype A] [DecidableEq A] [Nonempty A]

variable [Fintype B] [DecidableEq B] [Nonempty B]

variable [Fintype C] [DecidableEq C] [Nonempty C]

variable [Fintype D] [DecidableEq D] [Nonempty D]

/-- Lemma V.1, PDF pp.15--16: zero weights are permitted; EReal gives 0*infinity=0. -/
theorem mixture_entanglement (k : ℕ) (p : Fin k → ℝ)
    (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1) (hsum : ∑ i, p i = 1)
    (rho : Fin k → Mat (A × B)) (hrho : ∀ i, IsDensityMatrix (rho i)) :
    let average := ∑ i, (p i : ℂ) • rho i
    (∑ i, (p i : EReal) * eMax (rho i)) ≤
      eMax average + ∑ i, (p i : EReal) * maxRelative (rho i) average := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P25

end
