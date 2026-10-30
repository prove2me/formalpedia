-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P18_srm_completion
-- name    : QAlgorithms.Papers.Independent.Extend50.P18.srm_completion
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:00:26.378749+00:00
-- url     : https://prove2.me/theorems/e26e1064-76df-4be7-aa8a-e39fe42a4776
-- title:
--   Unnumbered §III: square-root POVM completion leaves fidelity unchanged
-- statement:
--   Let $d\ge1$, $k\ge1$, and $N\ge2k$, with normalized Bell resource, ordered outcome set $I$, signals $\sigma_i$, and $\rho=\sum_i\sigma_i$. Let $R=\rho^{-1/2}$ be the inverse square root on its support, zero on its kernel. Define $M_i=R\sigma_iR$, $\Delta=(I-\sum_iM_i)/|I|$, and $\Pi_i=M_i+\Delta$. Then
--
--   $$
--   \Pi_i\succeq0,\qquad\sum_i\Pi_i=I,\qquad
--   \frac1{d^{2k}}\sum_i\operatorname{Tr}(\Pi_i\sigma_i)
--   =\frac1{d^{2k}}\sum_i\operatorname{Tr}(M_i\sigma_i).
--   $$
--
--   Thus the completion is a valid deterministic POVM and leaves its entanglement fidelity unchanged. The raw effects are defined separately to remove the printed notation's self-reference.
-- source:
--   Efficient multi port-based teleportation schemes, arXiv:2008.00984v4, PDF p. 6, Unnumbered §III

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P18

noncomputable section

open scoped BigOperators Matrix ComplexOrder

namespace QAlgorithms.Papers.Independent.Extend50.P18

attribute [local instance] Classical.propDecidable

/-- SRM completion is a POVM and does not change entanglement fidelity. The raw
measurement has a separate definition, avoiding the self-reference of printed
(11) (PDF p.6, (10)-(11) and following paragraph). -/
theorem srm_completion (d N k : ℕ) (hd : 0 < d) (hk : 0 < k) (hports : 2*k ≤ N) :
    (∀ i : PortChoice N k, (srmEffect (d := d) i).PosSemidef) ∧
    (∑ i : PortChoice N k, srmEffect (d := d) i) = 1 ∧
    protocolFidelity (d := d) (N := N) (k := k) srmEffect =
      protocolFidelity (d := d) (N := N) (k := k) srmRaw := by sorry

end QAlgorithms.Papers.Independent.Extend50.P18

end
