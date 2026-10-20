-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P44_deterministic_capacity
-- name    : QAlgorithms.Papers.Independent.Dependency50.P44.deterministic_capacity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T15:33:06.905689+00:00
-- url     : https://prove2.me/theorems/97bd1d1e-2a70-45a8-8e99-9c7104a74b0c
-- title:
--   Single-letter assisted quantum capacity of deterministic classical channels
-- statement:
--   Let $\mathcal N:A'\to B_1B_2$ be a finite-dimensional deterministic classical broadcast channel. Thus, for fixed bases and arbitrary functions $f_j$ on input labels, its full quantum action dephases:
--
--   $$\mathcal N(\rho)=\sum_i\rho_{ii}|f_1(i)f_2(i)\rangle\langle f_1(i)f_2(i)|.$$
--
--   For a probability vector $p$, purify
--
--   $$\phi_p^{A_1A_2A'}=\sum_i p_i|f_1(i)\rangle\langle f_1(i)|\otimes|f_2(i)\rangle\langle f_2(i)|\otimes|i\rangle\langle i|$$
--
--   with the orthogonal flag $|i\rangle^D$, and let $\mathcal R_E(\phi_p,\mathcal N)$ be the three-inequality father region (9) computed from this input. Then the entanglement-assisted quantum capacity is
--
--   $$\mathcal C_E(\mathcal N)=\overline{\operatorname{conv}\!\left(\bigcup_p\mathcal R_E(\phi_p,\mathcal N)\right)}.$$
--
--   The operational region uses independent reference/message EPRs, arbitrary joint encoding, local decoding, vanishing joint error, and per-use liminf rates. The equality is stated for both literal purified source codes and the equivalent asymptotic CPTP presentation. This is a single-letter capacity result, with time sharing over $p$; it is not an unassisted quantum or confidential classical statement.
-- source:
--   A father protocol for quantum broadcast channels, arXiv:quant-ph/0612155v4, PDF p. 8, Theorem 5; channel and restricted inputs on p.7

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P44

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

open Filter Topology

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Dependency50.P44

open QAlgorithms.Papers.Independent.Information100.P58 (Operator)

open QAlgorithms.Papers.Independent.Information100.P67 (mapFirst)

/-- PDF pp.7–8, Theorem 5: deterministic classical channels have this single-letter
ENTANGLEMENT-ASSISTED QUANTUM capacity region, including the restricted input family proved
in VII and closed time sharing, in both equivalent asymptotic operational presentations.
The deterministic channel is dephasing, not a coherent map. -/
theorem deterministic_capacity {a : ℕ} {b : Fin 2 → ℕ} (N : Broadcast 2 a b)
    (f : (j : Fin 2) → BroadcastBasis a → BroadcastBasis (b j))
    (hN : N.channel = deterministicChannel f) :
    sourceQuantumCapacity N true = deterministicRegion N f ∧
      broadcastQuantumCapacity N true = deterministicRegion N f := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P44

end
