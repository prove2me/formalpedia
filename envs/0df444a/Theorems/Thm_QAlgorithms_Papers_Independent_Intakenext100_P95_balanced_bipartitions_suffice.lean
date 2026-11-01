-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P95_balanced_bipartitions_suffice
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P95.balanced_bipartitions_suffice
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T08:45:32.715991+00:00
-- url     : https://prove2.me/theorems/c4067cac-2677-4978-860f-13482790eb6a
-- title:
--   Balanced bipartitions suffice for a perfect tensor
-- statement:
--   Let $V$ be a finite local basis with $v=|V|\ge2$, and let $T$ be a complex tensor on $2n$ legs, for $n\ge0$. For a subset $A$ of legs, let $T_A$ denote the flattening with input legs $A$ and output legs $A^{\mathrm c}$. Suppose every balanced flattening is unitary. Then $T$ is nonzero and perfect:
--
--   $$\forall A,\ |A|\le n\ \Longrightarrow\ \exists c_A>0:\quad T_A^\dagger T_A=c_AI_A.$$
--
--   The balanced flattenings use the unitary normalization. Every balanced partition is tested, rather than a selected partition. At $n=0$ the assertion concerns a single nonzero scalar tensor.
-- source:
--   Holographic quantum error-correcting codes: Toy models for the bulk/boundary correspondence, arXiv:1503.06237v2, PDF p. 7, §2, balanced bipartitions suffice for perfection

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P95

namespace QAlgorithms.Papers.Independent.Intakenext100.P95

open scoped Matrix ComplexConjugate

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- PDF p.7 after Definition 2: all balanced unitary flattenings suffice.
The tensor has the balanced unitary normalization; the conclusion retains arbitrary
positive proportionality constants for smaller input subsets. Radius/arity zero is admitted. -/
theorem balanced_bipartitions_suffice {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (hv : 2 ≤ Fintype.card V) (T : EuclideanSpace ℂ (Fin (2 * n) → V))
    (hbalanced : ∀ A : Finset (Fin (2 * n)), A.card = n →
      (flatten T A)ᴴ * flatten T A = 1 ∧ (flatten T A) * (flatten T A)ᴴ = 1) :
    IsPerfect T := by sorry

end

end QAlgorithms.Papers.Independent.Intakenext100.P95
