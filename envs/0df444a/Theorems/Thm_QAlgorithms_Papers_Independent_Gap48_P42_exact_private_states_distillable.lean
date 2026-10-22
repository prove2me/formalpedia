-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P42_exact_private_states_distillable
-- name    : QAlgorithms.Papers.Independent.Gap48.P42.exact_private_states_distillable
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T05:35:24.257338+00:00
-- url     : https://prove2.me/theorems/b831e693-75aa-49ce-b077-9a2f12526041
-- title:
--   Every exact nontrivial private state has positive GHZ distillable entanglement
-- statement:
--   Let there be $N\ge2$ parties, a key dimension $d\ge2$, and positive finite local shield dimensions $s_1,\ldots,s_N$. Let $\rho$ be any positive semidefinite trace-one operator on the joint shield, and let $U_0,\ldots,U_{d-1}$ be arbitrary unitaries on that whole shield. Party $k$ owns its key and shield registers. The exact private state is
--
--   $$
--   \Gamma=\frac1d\sum_{i,j=0}^{d-1}|i,\ldots,i\rangle\langle j,\ldots,j|\otimes U_i\rho U_j^\dagger.
--   $$
--
--   Here $E_D$ is the supremum of nonnegative asymptotic rates of $N$-party qubit GHZ states obtained by trace-preserving adaptive LOCC, with full trace-norm error tending to zero and rate measured per input copy. Local ancillary systems, disposal and unrestricted two-way classical communication are allowed. The output used to define the rate includes all outcomes.
--
--   Then
--
--   $$
--   E_D(\Gamma)>0.
--   $$
--
--   For two parties the target is a Bell pair. This conclusion concerns each fixed exact finite private state; it makes no assertion about approximate private states with growing shields.
-- source:
--   Quantum states representing perfectly secure bits are always distillable, arXiv:quant-ph/0602176v2, PDF p. 1, Abstract; II.A–B

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P42

namespace QAlgorithms.Papers.Independent.Gap48.P42

open scoped BigOperators Matrix ComplexConjugate ComplexOrder ENNReal

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.1 abstract and II.A--B, pp.2--3: every exact finite private state
with at least two parties and key dimension at least two has strictly positive
asymptotic GHZ distillable entanglement. No approximate-private-state extension. -/
theorem exact_private_states_distillable {N d : ℕ} (hN : 2 ≤ N) (hd : 2 ≤ d)
    (S : Fin N → ℕ) (hS : ∀ k, 0 < S k)
    (rho : Matrix (PartyBasis S) (PartyBasis S) ℂ) (hrho : IsDensityMatrix rho)
    (U : Fin d → Matrix.unitaryGroup (PartyBasis S) ℂ) :
    0 < distillableGHZ (fun k => d * S k) (indexedPrivateDit rho U) := by sorry

end

end QAlgorithms.Papers.Independent.Gap48.P42
