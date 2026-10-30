-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P42_degradedDMC_partialStrongConverse
-- name    : QAlgorithms.Papers.Independent.Bridge50.P42.degradedDMC_partialStrongConverse
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T19:02:13.818187+00:00
-- url     : https://prove2.me/theorems/bb9d29ee-66c9-4d10-a39f-c44f2bcce52b
-- title:
--   Degraded DMC wiretap channels: partial strong converse
-- statement:
--   Let $\mathcal X,\mathcal Y,\mathcal Z$ be finite nonempty alphabets and $W(y,z\mid x)=W_Y(y\mid x)W_2(z\mid y)$ a normalized degraded stationary memoryless channel. Its Eve marginal is $W_Z(z\mid x)=\sum_yW_Y(y\mid x)W_2(z\mid y)$. All quantities are in bits. Set
--
--   $$C_s(W)=\max_{P_X}\{I(X;Y)-I(X;Z)\},\qquad C(W_Y)=\max_{P_X}I(X;Y).$$
--
--   The maximum defining $C_s$ is attained. For the six literal metrics of Definition 1, define
--
--   $$C_i=\begin{cases}C(W_Y),&i=5,\\C_s(W),&i=1,2,3,4,6.\end{cases}$$
--
--   Let $C_\varepsilon^{(i)}$ and $\overline C_\varepsilon^{(i)}$ be the ordinary and optimistic operational capacities of Definitions 2–4: finite positive uniform messages, arbitrary stochastic encoders, deterministic decoders, average error, and vanishing leakage, with one code sequence satisfying every positive threshold for tail metrics. Then
--
--   $$C_0^{(i)}=\overline C_1^{(i)}=C_i,$$
--   $$C_\varepsilon^{(i)}=C_i\ (0\le\varepsilon<1),\qquad \overline C_\varepsilon^{(i)}=C_i\ (0<\varepsilon\le1).$$
--
--   Source correction: the printed theorem assigns $C_s$ to every metric. Its printed $S_5=V(P,Q)/n$ vanishes for every code because variational distance $V\le1$, so only that metric's common value is changed to Bob's capacity.
-- source:
--   Information Spectrum Approach to Strong Converse Theorems for Degraded Wiretap Channels, arXiv:1406.6758v2, PDF p. 5, Theorem 3 (Degraded DM-WTCs)

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P42

noncomputable section

namespace QAlgorithms.Papers.Independent.Bridge50.P42

open Filter

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

open QAlgorithms.Papers.Independent.Information100.P80 (log2)

attribute [local instance] Classical.propDecidable

/-- PDF p.5, Theorem 3, with endpoint equality and its full epsilon consequences
from p.4, (27)–(29). All finite alphabets are nonempty. Equation (41)'s maximum
is attained; its difference form uses the actual two marginals.
SOURCE CORRECTION (trap 30): printed Theorem 3 assigns CsDM to all six metrics.
Changed only S5's capacity value to C(W.main), preserving printed S5=variation/n.
Why: variation<=1 makes S5 vanish for every code; noiseless identical binary
Bob/Eve channels have zero secrecy capacity but S5 capacity one. -/
theorem degradedDMC_partialStrongConverse
    {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    [Nonempty X] [Nonempty Y] [Nonempty Z] (W : DegradedDMC X Y Z) :
    (∃ p : X → ℝ, IsLaw p ∧ secrecyInfo W p = secrecyCapacity W) ∧
    ∀ i : SecrecyMetric, CapacityConclusion (fun _ => W) i
      (if i = .normalizedVariation then finiteChannelCapacity W.main else secrecyCapacity W) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P42

end
