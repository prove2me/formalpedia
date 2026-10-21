-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P38_dephasingSideChannel_noQuantumGain
-- name    : QAlgorithms.Papers.Independent.Claimed50.P38.dephasingSideChannel_noQuantumGain
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T10:41:17.297838+00:00
-- url     : https://prove2.me/theorems/e09f7c07-42de-420c-a219-1ec41f3794e2
-- title:
--   A dephasing side channel cannot increase unassisted quantum capacity
-- statement:
--   Let $d\ge2$ and $\Delta\ge1$ be integers, let $\mathcal M$ be a completely positive trace-preserving map on a $d$-dimensional Hilbert space, and let $\mathcal T$ be complete dephasing on a fixed $\Delta$-dimensional basis. Let $Q_d(\mathcal N)$ denote the operational unassisted quantum capacity of a memoryless channel $\mathcal N$, in base-$d$ qudits per actual channel use: an encoding and decoding channel are fixed before the unknown input, their uniform pure-state transmission fidelity tends to one, and capacity is the nonnegative extended supremum of achievable asymptotic rates. Arbitrary local ancillas are allowed, with no shared entanglement or side communication. Then
--
--   $$
--   Q_d(\mathcal M\otimes\mathcal T)\le Q_d(\mathcal M).
--   $$
--
--   Both sides use the same logical base $d$, even though the left physical input has dimension $d\Delta$. This is the operational no-increase inequality needed in the forward-assistance argument; it imposes no simulation-specific lower bound $\Delta\ge d^y$.
-- source:
--   Inequalities for quantum channels assisted by limited resources, arXiv:quant-ph/0406111v3, PDF p. 4, §II B Eq.(16): a dephasing side channel cannot increase quantum capacity

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P38

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P38

open scoped ComplexConjugate Matrix

open Filter

open QAlgorithms.Papers.Independent.Information100.P58 (Word)

/-- Giovannetti, arXiv:quant-ph/0406111v3, PDF p.4, Eq.(16).
A positive-dimensional completely dephasing side channel cannot increase
unassisted quantum capacity. Both capacities use the ORIGINAL base d.
The stronger simulation condition delta >= d^y is not needed for this inequality. -/
theorem dephasingSideChannel_noQuantumGain
    (d delta : ℕ) (hd : 2 ≤ d) (hdelta : 0 < delta)
    (M : Superop (Fin d) (Fin d)) (hM : IsChannel M) :
    unassistedQuantumCapacityD d (tensorSuperop M (completeDephasing (A := Fin delta))) ≤
      unassistedQuantumCapacityD d M := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P38

end
