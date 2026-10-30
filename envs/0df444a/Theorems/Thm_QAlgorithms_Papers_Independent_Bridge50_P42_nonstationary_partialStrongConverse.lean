-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P42_nonstationary_partialStrongConverse
-- name    : QAlgorithms.Papers.Independent.Bridge50.P42.nonstationary_partialStrongConverse
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T19:02:53.870869+00:00
-- url     : https://prove2.me/theorems/c906754c-9bd4-4f17-adf6-3b943689e7c7
-- title:
--   Weakly symmetric nonstationary wiretap channels
-- statement:
--   Fix finite nonempty alphabets and normalized degraded components $W_j(y,z\mid x)=W_{Y,j}(y\mid x)W_{2,j}(z\mid y)$, with Eve marginals $W_{Z,j}(z\mid x)=\sum_yW_{Y,j}(y\mid x)W_{2,j}(z\mid y)$. The length-$n$ channel is the product of its first $n$ components. Assume every Bob and Eve marginal is weakly symmetric: rows are permutations of one another and column sums are constant. Write $C(V)=\max_{P_X}I(X;V(X))$, in bits, and suppose the separate real limits
--
--   $$L_Y=\lim_{n\to\infty}\frac1n\sum_{j=1}^nC(W_{Y,j}),\qquad L_Z=\lim_{n\to\infty}\frac1n\sum_{j=1}^nC(W_{Z,j})$$
--
--   exist. For each literal secrecy metric of Definition 1 set
--
--   $$C_i=\begin{cases}L_Y,&i=5,\\L_Y-L_Z,&i=1,2,3,4,6.\end{cases}$$
--
--   Using the ordinary and strict optimistic operational capacities from Definitions 2–4, with arbitrary stochastic encoding, average error, vanishing leakage and every positive tail threshold for one sequence,
--
--   $$C_0^{(i)}=\overline C_1^{(i)}=C_i,$$
--   $$C_\varepsilon^{(i)}=C_i\ (0\le\varepsilon<1),\qquad\overline C_\varepsilon^{(i)}=C_i\ (0<\varepsilon\le1).$$
--
--   This retains the sufficient partial strong converse of Theorem 4. Source correction: the proof's all-six value $L_Y-L_Z$ is changed only for literal $S_5=V/n$, which imposes no secrecy restriction. No necessity or uniqueness of maximizing input is asserted.
-- source:
--   Information Spectrum Approach to Strong Converse Theorems for Degraded Wiretap Channels, arXiv:1406.6758v2, PDF p. 5, Theorem 4 (Non-Stationary Wiretap Channels)

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P42

noncomputable section

namespace QAlgorithms.Papers.Independent.Bridge50.P42

open Filter

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

open QAlgorithms.Papers.Independent.Information100.P80 (log2)

attribute [local instance] Classical.propDecidable

/-- PDF pp.5–6, Theorem 4; the quantitative common value follows from
(82)–(83), p.9. Each marginal is weakly symmetric; neither factor W2 nor
uniqueness of a maximizing input is assumed. Separate real limits are required.
SOURCE CORRECTION (trap 30): printed proof pp.9-11 assigns CY-CZ to all six metrics.
Changed only S5's common value to CY, retaining the partial strong converse for
all six. Why: printed S5=variation/n is automatically vanishing for every code,
so its ordinary/optimistic capacities are Bob's capacities, not secrecy capacities. -/
theorem nonstationary_partialStrongConverse
    {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    [Nonempty X] [Nonempty Y] [Nonempty Z]
    (W : ℕ → DegradedDMC X Y Z)
    (hmain : ∀ j, WeaklySymmetric (W j).main)
    (heve : ∀ j, WeaklySymmetric (W j).eve)
    (CY CZ : ℝ)
    (hCY : Tendsto (capacityAverage (fun j => (W j).main)) atTop (nhds CY))
    (hCZ : Tendsto (capacityAverage (fun j => (W j).eve)) atTop (nhds CZ)) :
    ∀ i : SecrecyMetric, CapacityConclusion W i
      (if i = .normalizedVariation then CY else CY - CZ) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P42

end
