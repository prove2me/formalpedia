-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P15_thermal_gap_bound
-- name    : QAlgorithms.Papers.Independent.Gap20.P15.thermal_gap_bound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T07:21:52.695805+00:00
-- url     : https://prove2.me/theorems/a0464e6d-600d-49f1-9fb3-209f3ceff249
-- title:
--   Theorem 26: thermal gap bound
-- statement:
--   Write $g(x)=((x+1)\ln(x+1)-x\ln x)/\ln2$ for thermal entropy in bits, with $g(0)=0$.
--
--   Let $1/2\le\eta\le1$, $N_B\ge0$, and $N_S\ge0$ be finite real parameters. Set $t=\eta/[1+(1-\eta)N_B]$, $U_1=g(tN_S)-g((1-t)N_S)$, and $D=\sqrt{((1+\eta)N_S+(1-\eta)N_B+1)^2-4\eta N_S(N_S+1)}$. Define $L=g(\eta N_S+(1-\eta)N_B)-g((D+(1-\eta)(N_S-N_B)-1)/2)-g((D-(1-\eta)(N_S-N_B)-1)/2)$. Then
--
--   $$L\le U_1\le L+\frac1{\ln2}.$$
--
--   This compares the raw scalar expressions, including the identity-channel and vacuum endpoints. It makes no assertion of fixed-channel saturation of the constant.
-- source:
--   Bounding the energy-constrained quantum and private capacities of phase-insensitive bosonic Gaussian channels, arXiv:1708.07257v3, PDF p. 34, Theorem 26

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P15

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap20.P15

open QAlgorithms.Papers.Independent.Frontier30.P24 (bosonicEntropy)

open QAlgorithms.Papers.Independent.Dependency50.P33 (State)

open QAlgorithms.Papers.Independent.Frontier18.P01 (Channel Hamiltonian)

open QAlgorithms.Papers.Independent.Gap48.P26 (entropyBits)

open QAlgorithms.Papers.Independent.Claimed50.P35 (traceClassChannelPower)

open scoped ENNReal

/-- Theorem 26, PDF p.34, (6.3). Raw U1 and L, including eta=1, NB=0,
and NS=0. The incorrect fixed-channel saturation claim on pp.34-35 is deferred. -/
theorem thermal_gap_bound (eta noise energy : ℝ)
    (heta : 1 / 2 ≤ eta) (heta1 : eta ≤ 1)
    (hnoise : 0 ≤ noise) (henergy : 0 ≤ energy) :
    thermalCoherent eta noise energy ≤ thermalDataProcessing eta noise energy ∧
    thermalDataProcessing eta noise energy ≤
      thermalCoherent eta noise energy + 1 / Real.log 2 := by sorry

end QAlgorithms.Papers.Independent.Gap20.P15

end
