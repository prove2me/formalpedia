-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P32_energyAmplificationSet_compact
-- name    : QAlgorithms.Papers.Independent.Claimed50.P32.energyAmplificationSet_compact
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T10:28:36.11277+00:00
-- url     : https://prove2.me/theorems/c998d927-87f1-4985-b160-fe94e6a100c2
-- title:
--   Channels with bounded energy amplification form a compact set
-- statement:
--   Let $G_{\mathrm{in}}$ and $G_{\mathrm{out}}$ be nonnegative Hamiltonians on nonzero separable complex Hilbert spaces, each with a complete eigenbasis and finite eigenvalue sublevel sets. Fix $k>0$. Let $F_k$ consist of all channels satisfying
--
--   $$\operatorname{Tr}(G_{\mathrm{out}}\Phi(\rho))\leq k\operatorname{Tr}(G_{\mathrm{in}}\rho)\quad\text{for every finite-energy input state }\rho.$$
--
--   Then $F_k$ is compact in the strong topology. This is the energy-amplification set of (12), interpreted by its homogeneous physical inequality also when the input energy is zero. That convention avoids the undefined zero denominator in the printed quotient.
-- source:
--   On approximation of quantum channels, arXiv:0711.2245v1, PDF p. 10, §3, Example 2, (12): compact bounded energy amplification

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P32

noncomputable section

open Filter

open scoped Topology ENNReal NNReal BigOperators

namespace QAlgorithms.Papers.Independent.Claimed50.P32

open QAlgorithms.RealRegisters (Hilbert)

/-- §3, Example 2 and (12), PDF p.10: the bounded-energy-amplification
channel set is strongly compact. The homogeneous convention includes zero
input energy, where the source's quotient is undefined. -/
theorem energyAmplificationSet_compact {I J : Type}
    [Countable I] [Nonempty I] [Countable J] [Nonempty J] (energyIn : I → ℝ≥0)
    (energyOut : J → ℝ≥0) (hin : IsEnergyOperator energyIn)
    (hout : IsEnergyOperator energyOut) (k : ℝ) (hk : 0 < k) :
    IsCompact (boundedAmplification energyIn energyOut k) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P32

end
