-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P49_unruh_classicalCapacity
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P49.unruh_classicalCapacity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:29:46.06198+00:00
-- url     : https://prove2.me/theorems/3dc933d9-9d0d-47de-abc6-9048b71964cd
-- title:
--   Corollary 3 / Eq.(23): classical capacity of the full Unruh channel
-- statement:
--   Let $0\le z<1$, $p_\ell=(1-z)^3z^{\ell-2}\ell(\ell-1)/2$, and $\Delta_\ell=\ell(\ell-1)/2$. Let $U_z$ be the full countable flagged qubit-input Unruh channel. Its classical capacity, independently defined by regularized Holevo optimization over arbitrary finite ensembles and entangled positive-block-length inputs, is
--
--   $$
--   C(U_z)=1-\sum_{\ell=2}^{\infty}p_\ell\log_2(\ell-1)
--   +\sum_{\ell=2}^{\infty}\frac{p_\ell}{\Delta_\ell}\sum_{j=0}^{\ell-1}j\log_2j.
--   $$
--
--   Both infinite series converge separately, and the output entropies and optimization suprema satisfy the regularity assertions of Theorem 2. The zero summand uses $0\log_2 0=0$. At $z=0$ only the identity sector has positive weight and the expression is $1$ bit. This gives the capacity of the full channel, with no finite cutoff or value assigned at $z=1$.
-- source:
--   An Infinite Sequence of Additive Channels: the Classical Capacity of Cloning Channels, arXiv:0903.1638v7, PDF p. 5, Corollary 3 / Eq.(23)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P49

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P49

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

open Filter

open QAlgorithms.Papers.Independent.Support50.P01
  (unruhSectorDilation unruhWeight unruhBlockDilation unruhBlockWeight
   unruhReceiver unruhReceiverEntropy)

open QAlgorithms.Papers.Independent.Information100.P67
  (receiverChannel complementaryChannel IsDegradable)

open QAlgorithms.Papers.Independent.Dependency50.P41 (EntanglementBreaking)

open QAlgorithms.Papers.Independent.Dependency50.P40 (outputFirstChoi)

open QAlgorithms.Papers.Independent.Dependency50.P45 (holevoCapacity)

open QAlgorithms.Papers.Independent.Information100.P62 (tensorChannel)

open QAlgorithms.QuditFidelity (depolarizingMap)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.5, Corollary 3, Eq.(23): separately convergent signed series for
the independently regularized capacity; z=1 is excluded. -/
theorem unruh_classicalCapacity (z : ℝ) (_hz0 : 0 ≤ z) (_hz1 : z < 1) :
    UnruhRegular z ∧ Summable (unruhFirstTerm z) ∧ Summable (unruhSecondTerm z) ∧
    unruhClassicalCapacity z =
      1 - (∑' k : ℕ, unruhFirstTerm z k) + (∑' k : ℕ, unruhSecondTerm z k) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P49

end
