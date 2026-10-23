-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P15_amplifier_gap_bound
-- name    : QAlgorithms.Papers.Independent.Gap20.P15.amplifier_gap_bound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T07:23:45.120075+00:00
-- url     : https://prove2.me/theorems/2c5d1866-1a80-47c5-82f8-eda9e8d99ff0
-- title:
--   Theorem 35: amplifier gap bound
-- statement:
--   Write $g(x)=((x+1)\ln(x+1)-x\ln x)/\ln2$ for thermal entropy in bits, with $g(0)=0$.
--
--   Let $G>1$, $N_B,N_S\ge0$, and $(G-1)N_B<1$, all finite. Set $G'=G/[1-(G-1)N_B]$ and $U_1=g(G'N_S+G'-1)-g((G'-1)(N_S+1))$. Put $D=\sqrt{((1+G)N_S+(G-1)(N_B+1)+1)^2-4GN_S(N_S+1)}$ and $L=g(GN_S+(G-1)(N_B+1))-g((D+(G-1)(N_S+N_B+1)-1)/2)-g((D-(G-1)(N_S+N_B+1)-1)/2)$. Then
--
--   $$L\le U_1\le L+\frac1{\ln2}.$$
--
--   Both expressions are raw scalar values. This bounds their separation uniformly over the stated parameters.
-- source:
--   Bounding the energy-constrained quantum and private capacities of phase-insensitive bosonic Gaussian channels, arXiv:1708.07257v3, PDF p. 45, Theorem 35

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P15

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap20.P15

open QAlgorithms.Papers.Independent.Frontier30.P24 (bosonicEntropy)

open QAlgorithms.Papers.Independent.Dependency50.P33 (State)

open QAlgorithms.Papers.Independent.Frontier18.P01 (Channel Hamiltonian)

open QAlgorithms.Papers.Independent.Gap48.P26 (entropyBits)

open QAlgorithms.Papers.Independent.Claimed50.P35 (traceClassChannelPower)

open scoped ENNReal

/-- Theorem 35, PDF p.45, (9.22), using (9.10)-(9.11) and (9.20)-(9.21).
The strict non-entanglement-breaking condition keeps the gain denominator positive. -/
theorem amplifier_gap_bound (gain noise energy : ℝ)
    (hgain : 1 < gain) (hnoise : 0 ≤ noise) (henergy : 0 ≤ energy)
    (hphysical : (gain - 1) * noise < 1) :
    amplifierCoherent gain noise energy ≤ amplifierDataProcessing gain noise energy ∧
    amplifierDataProcessing gain noise energy ≤
      amplifierCoherent gain noise energy + 1 / Real.log 2 := by sorry

end QAlgorithms.Papers.Independent.Gap20.P15

end
