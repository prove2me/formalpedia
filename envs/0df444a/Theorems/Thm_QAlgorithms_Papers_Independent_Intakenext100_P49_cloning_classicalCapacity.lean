-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P49_cloning_classicalCapacity
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P49.cloning_classicalCapacity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:26:45.994204+00:00
-- url     : https://prove2.me/theorems/045d788e-677c-48d5-9d84-58e93ef68221
-- title:
--   Corollary 2 / Eq.(16): classical capacity of the cloning channels
-- statement:
--   Let $\ell\ge2$ be an integer and set $\Delta_\ell=\ell(\ell-1)/2$. Define $C(N)$ independently by regularizing the Holevo capacity over all positive tensor powers, allowing arbitrary finite ensembles of entangled inputs. The classical capacity in bits of the full symmetric cloning output is
--
--   $$
--   C(\mathrm{Cl}_{1,\ell-1})=1-\log_2(\ell-1)+\frac{1}{\Delta_\ell}\sum_{j=0}^{\ell-1}j\log_2j.
--   $$
--
--   The convention is $0\log_2 0=0$. The formula yields $1$ bit at $\ell=2$ and $2/3$ bit at $\ell=3$. It evaluates the regularized capacity rather than defining capacity by the displayed expression.
--
--   **Formalization Note** Regularization is the supremum of positive block rates, equivalent to the source limit by superadditivity and boundedness.
-- source:
--   An Infinite Sequence of Additive Channels: the Classical Capacity of Cloning Channels, arXiv:0903.1638v7, PDF p. 4, Corollary 2 / Eq.(16)

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

/-- PDF p.4, Corollary 2, Eq.(16): regularized classical capacity in bits. -/
theorem cloning_classicalCapacity (k : ℕ) :
    classicalCapacityBits (cloner k) =
      1 - Real.logb 2 (k+1 : ℝ) + clonerLogSum k / clonerDelta k := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P49

end
