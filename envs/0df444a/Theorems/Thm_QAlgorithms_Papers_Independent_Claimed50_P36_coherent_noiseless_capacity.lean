-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P36_coherent_noiseless_capacity
-- name    : QAlgorithms.Papers.Independent.Claimed50.P36.coherent_noiseless_capacity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T10:34:10.791781+00:00
-- url     : https://prove2.me/theorems/28f2413c-a60b-47f2-9b1a-073b0549e579
-- title:
--   Noiseless continuous coherent-alphabet capacity
-- statement:
--   Consider the noiseless one-mode channel whose letters are every coherent state $|\alpha\rangle$, $\alpha\in\mathbb C$. The transmitted mean photon budget is $m\ge0$. Codes use product letters, satisfy the transmitted photon constraint, and admit arbitrary collective POVMs with asymptotically vanishing error. The coherent overlap obeys $|\langle\alpha|\beta\rangle|^2=e^{-|\alpha-\beta|^2}$. Its classical capacity in nats per mode is
--
--   $$
--   C_{\rm BE}(m)=g(m)=(m+1)\log(m+1)-m\log m.
--   $$
--
--   Here $0\log0=0$, so $C_{\rm BE}(0)=0$. The feasible rate set is bounded above. This is the continuous coherent-alphabet reference rate for the paper's binary discretizations.
-- source:
--   Information capacity formula of quantum optical channels, arXiv:quant-ph/0105042v1, PDF p. 16, Eq.(67)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P36

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P36

open Filter

open scoped Topology ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable

-- Reuse the pinned accepted entropy definitions, preserving their codomains
-- and units. P24.bosonicEntropy is in bits: multiply by log 2 for nats.
-- P01.binaryEntropy is in nats and ENNReal-valued: use toReal only at the
-- finite binary-probability argument of binaryValue below.

open QAlgorithms.Papers.Independent.Frontier30.P24 (bosonicEntropy)

open QAlgorithms.Papers.Independent.Frontier18.P01 (binaryEntropy)

/-- PDF p.16, Eq.(67), with pp.3,7 transmitter constraint and collective POVMs:
noiseless continuous coherent-alphabet operational capacity, in nats. -/
theorem coherent_noiseless_capacity (m : ℝ) (hm : 0 ≤ m) :
    BddAbove (coherentRates m) ∧ coherentCapacity m = (Real.log 2 * bosonicEntropy m) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P36

end
