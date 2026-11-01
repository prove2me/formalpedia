-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P14_split_channel_recursion
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P14.split_channel_recursion
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T04:57:20.174842+00:00
-- url     : https://prove2.me/theorems/2a136d69-1c98-4523-923a-40c058dd4c90
-- title:
--   Exact split recursion with the classical flag and history maps
-- statement:
--   Let $W$ be a binary-input classical–quantum channel, let $N=2^n$, $n\ge0$, and $1\le i\le N$. Put $V=W_N^{(i)}$. Its bad transform averages the second bit, and its good transform retains the first bit as a classical output:
--
--   $$V^-(b)=\frac12\sum_c V(b\oplus c)\otimes V(c),\qquad
--   V^+(c)=\frac12\sum_b |b\rangle\langle b|\otimes V(b\oplus c)\otimes V(c).$$
--
--   For histories $s,t$ of length $i-1$, relabel the two old history registers by interleaving $s\oplus t$ and $t$. Keep the physical outputs in their first-$N$, last-$N$ order. In the good case, append the newly exposed odd bit to the interleaved history. Write $\mathcal R_-$ and $\mathcal R_+$ for these concrete basis relabelings. Both exact identities hold:
--
--   $$W_{2N}^{(2i-1)}=\mathcal R_-(V^-),\qquad W_{2N}^{(2i)}=\mathcal R_+(V^+).$$
--
--   This is the recursion asserted in (16), with registers restored using (6)–(8) and (14)–(15). Printed (18) omits the sum and classical flag; the formal statement records the corrected channel identity rather than that ill-typed expression.
-- source:
--   Polar codes for classical-quantum channels, arXiv:1109.2591v3, PDF p. 7, Proposition 7: exact split-channel recursion, with the missing classical register restored

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P14

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P14

open Filter MeasureTheory

open scoped ENNReal NNReal ComplexOrder BigOperators

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33 (IsDensity)

open QAlgorithms.Papers.Independent.Dependency50.P13 (compression)

open QAlgorithms.Papers.Independent.Renew46.P44 (wordOutput)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Proposition 7, PDF p.7, corrected (17)–(18). Printed (18) omits the
uniform sum and new odd-bit classical flag, leaving an unbound bit. Changed:
use exactly (14)–(16), pulling back by the concrete history/output maps above.
Why: already N=i=1 the printed spaces disagree; definitions (6)–(8) uniquely
fix this correction. Both exact recursive identities are included. Independent
moderation of this source correction remains required. -/
theorem split_channel_recursion {I : Type} (W : Bit → OutputCoefficients I) (hW : IsBinaryCqChannel W)
    (n : ℕ) (i : PolarWire n) :
    (∀ b (p q : SplitLabel I (n + 1) (childIndex i false)),
      splitChannel W (n + 1) (childIndex i false) b p q =
        channelMinus (splitChannel W n i) b (parentLabels i false p) (parentLabels i false q)) ∧
    (∀ b (p q : SplitLabel I (n + 1) (childIndex i true)),
      splitChannel W (n + 1) (childIndex i true) b p q =
        channelPlus (splitChannel W n i) b (plusLabel i p) (plusLabel i q)) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P14

end
