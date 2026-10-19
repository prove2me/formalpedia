-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P62_capacity_converses
-- name    : QAlgorithms.Papers.Independent.Information100.P62.capacity_converses
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T21:39:56.562921+00:00
-- url     : https://prove2.me/theorems/18dc5104-6293-4e5c-bd68-58ebed297ac8
-- title:
--   Lemma 3.10: three capacity converses
-- statement:
--   If $A=\bigoplus_kM_{d_k}(\mathbb C)$ is transmittable through a channel $\Phi$, then its block sizes obey all three one-shot zero-error capacity bounds:
--   $$\log_2\max_kd_k\le Q_0(\Phi),\quad\log_2\sum_kd_k\le C_0(\Phi),\quad\log_2\sum_kd_k^2\le C_0^{\rm ea}(\Phi).$$
--   All optimizations are exact and the assisted capacity allows arbitrary finite entanglement.
-- source:
--   Transmitting algebras through quantum channels, arXiv:2609.40054v1, PDF p. 27, Lemma 3.10: three capacity converses

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P62

namespace QAlgorithms.Papers.Independent.Information100.P62

noncomputable section

open scoped ComplexConjugate Matrix ComplexOrder

open Finset

attribute [local instance] Classical.propDecidable

variable {I O J K : Type} [Fintype I] [Fintype O] [Fintype J] [Fintype K]

variable [DecidableEq I] [DecidableEq O] [DecidableEq J] [DecidableEq K]

/-- arXiv:2609.40054v1, PDF pp.27, Lemma 3.10: three capacity converses. -/
theorem capacity_converses [Nonempty I] [Nonempty O]
    (F : Superop I O) (hF : IsChannel F) (A : Shape) (hA : Transmits F A) :
    logTwo ((A.toList.foldl max 0 : ℕ) : ℝ) ≤ quantumCapacity F ∧
    logTwo (lengthDim A) ≤ classicalCapacity F ∧
    logTwo (((A.map (fun d : ℕ => d ^ 2)).sum : ℕ) : ℝ) ≤ assistedCapacity F := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P62
