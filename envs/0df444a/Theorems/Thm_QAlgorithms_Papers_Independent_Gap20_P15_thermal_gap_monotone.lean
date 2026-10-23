-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P15_thermal_gap_monotone
-- name    : QAlgorithms.Papers.Independent.Gap20.P15.thermal_gap_monotone
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T07:23:06.593382+00:00
-- url     : https://prove2.me/theorems/fd08d9ac-3a90-4555-893a-81e19534e37b
-- title:
--   Unnumbered gap monotonicity: thermal gap monotone
-- statement:
--   Write $g(x)=((x+1)\ln(x+1)-x\ln x)/\ln2$ for thermal entropy in bits, with $g(0)=0$.
--
--   Let $1/2\le\eta\le1$, $N_B\ge0$, and $N_S\ge0$ be finite real parameters. Set $t=\eta/[1+(1-\eta)N_B]$, $U_1=g(tN_S)-g((1-t)N_S)$, and $D=\sqrt{((1+\eta)N_S+(1-\eta)N_B+1)^2-4\eta N_S(N_S+1)}$. Define $L=g(\eta N_S+(1-\eta)N_B)-g((D+(1-\eta)(N_S-N_B)-1)/2)-g((D-(1-\eta)(N_S-N_B)-1)/2)$. For fixed $\eta,N_B$, put $\Delta(N_S)=U_1(N_S)-L(N_S)$. Then
--
--   $$0\le N_S\le N'_S\quad\Longrightarrow\quad\Delta(N_S)\le\Delta(N'_S).$$
--
--   This controls input-energy dependence without asserting the incorrect saturation limit. The pure-loss gap is identically zero.
-- source:
--   Bounding the energy-constrained quantum and private capacities of phase-insensitive bosonic Gaussian channels, arXiv:1708.07257v3, PDF p. 35, Unnumbered gap monotonicity

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P15

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap20.P15

open QAlgorithms.Papers.Independent.Frontier30.P24 (bosonicEntropy)

open QAlgorithms.Papers.Independent.Dependency50.P33 (State)

open QAlgorithms.Papers.Independent.Frontier18.P01 (Channel Hamiltonian)

open QAlgorithms.Papers.Independent.Gap48.P26 (entropyBits)

open QAlgorithms.Papers.Independent.Claimed50.P35 (traceClassChannelPower)

open scoped ENNReal

/-- Unnumbered monotonicity claim, PDF pp.35-36, (6.22)-(6.25): increasing
means nondecreasing, allowing the identically-zero pure-loss gap. -/
theorem thermal_gap_monotone (eta noise : ℝ)
    (heta : 1 / 2 ≤ eta) (heta1 : eta ≤ 1) (hnoise : 0 ≤ noise) :
    MonotoneOn (thermalGap eta noise) (Set.Ici (0 : ℝ)) := by sorry

end QAlgorithms.Papers.Independent.Gap20.P15

end
