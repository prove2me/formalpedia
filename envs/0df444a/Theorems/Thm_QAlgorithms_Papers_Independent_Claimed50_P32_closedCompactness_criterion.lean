-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P32_closedCompactness_criterion
-- name    : QAlgorithms.Papers.Independent.Claimed50.P32.closedCompactness_criterion
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T10:26:30.057988+00:00
-- url     : https://prove2.me/theorems/42f6cf46-51f1-4822-923f-d22e40c1cb4a
-- title:
--   Corrected compactness criterion for strongly closed operation sets
-- statement:
--   Let $F$ be a strongly closed set of quantum operations between nonzero separable complex Hilbert spaces, and let $\sigma$ be any faithful input state (its kernel is zero). Then
--
--   $$F\text{ is strongly compact}\quad\Longleftrightarrow\quad\{\Phi(\sigma):\Phi\in F\}\text{ is trace-norm compact}.$$
--
--   Moreover, strong compactness of $F$ implies trace-norm compactness of $\{\Phi(\rho):\Phi\in F\}$ for every input state $\rho$. This is a disclosed repair of Corollary 2: its printed sufficient direction omits the necessary closedness assumption. The uncorrected node is deferred separately.
-- source:
--   On approximation of quantum channels, arXiv:0711.2245v1, PDF p. 9, §3, Corollary 2: corrected closed-subset version

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P32

noncomputable section

open Filter

open scoped Topology ENNReal NNReal BigOperators

namespace QAlgorithms.Papers.Independent.Claimed50.P32

open QAlgorithms.RealRegisters (Hilbert)

/-- §3, Corollary 2, PDF p.9, corrected version: strong closedness is added
because the printed sufficient direction is false for nonclosed subsets.
For a strongly closed set, compactness is equivalent to compact evaluation at
any given faithful state; compact sets have compact evaluation at every state. -/
theorem closedCompactness_criterion {I J : Type}
    [Countable I] [Nonempty I] [Countable J] [Nonempty J] (F : Set (CanonicalOperation I J)) (hclosed : IsClosed F)
    (sigma : Nuclear.State I) (hfaithful : Operators.HasFullSupport sigma) :
    (IsCompact F ↔ IsCompact (evaluationImage F sigma)) ∧
    (IsCompact F → ∀ rho : Nuclear.State I, IsCompact (evaluationImage F rho)) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P32

end
