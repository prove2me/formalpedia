-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P62_zero_quantum_domination
-- name    : QAlgorithms.Papers.Independent.Information100.P62.zero_quantum_domination
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-18T21:53:50.168504+00:00
-- url     : https://prove2.me/theorems/e85efa30-334d-45e3-be08-e495e99bbe89
-- title:
--   Theorem 4.21: zero quantum capacity
-- statement:
--   If a channel $\Phi$ has one-shot zero-error quantum capacity $Q_0(\Phi)=0$, then
--   $$A_{\rm dom}(\Phi)\cong\mathbb C^{\alpha(S_\Phi)}=\mathbb C^{2^{C_0(\Phi)}}.$$
--   The exponent in the finite direct sum is the integer message optimum $\alpha(S_\Phi)$. This identifies a dominating classical memory.
-- source:
--   Transmitting algebras through quantum channels, arXiv:2609.40054v1, PDF p. 42, Theorem 4.21: zero quantum capacity

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P62

namespace QAlgorithms.Papers.Independent.Information100.P62

noncomputable section

open scoped ComplexConjugate Matrix ComplexOrder

open Finset

attribute [local instance] Classical.propDecidable

variable {I O J K : Type} [Fintype I] [Fintype O] [Fintype J] [Fintype K]

variable [DecidableEq I] [DecidableEq O] [DecidableEq J] [DecidableEq K]

/-- arXiv:2609.40054v1, PDF pp.42, Theorem 4.21: zero quantum capacity. -/
theorem zero_quantum_domination [Nonempty I] [Nonempty O]
    (F : Superop I O) (hF : IsChannel F) (hzero : quantumCapacity F = 0) :
    Dominating F (classical (alpha (graph F))) := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P62
