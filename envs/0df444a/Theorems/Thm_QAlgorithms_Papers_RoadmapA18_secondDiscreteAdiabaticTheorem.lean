-- Prove2me | Theorems.Thm_QAlgorithms_Papers_RoadmapA18_secondDiscreteAdiabaticTheorem
-- name    : QAlgorithms.Papers.RoadmapA18.secondDiscreteAdiabaticTheorem
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T18:48:33.178743+00:00
-- url     : https://prove2.me/theorems/06d136ab-02ff-482a-8ce2-b2bd91e02468
-- title:
--   The Second Discrete Adiabatic Theorem: an explicit operator-norm error bound
-- statement:
--   Let $\mathcal H$ be a complete complex Hilbert space and $T\ge1$ an integer. Write $W_j=W_T(j/T)$ for unitary walk operators on $\mathcal H$, for $0\le j\le T$. Choose at each step a spectral band $\sigma_P(j)$ and its complement $\sigma_Q(j)$. For each valid window $j,j+1,\ldots,j+k$, with $k=0,1,2$, enclose the two bands in disjoint closed proper arcs of the unit circle. Use compatible choices in which shorter-window arcs lie in the corresponding longer-window arcs. Let $\Delta_k(j)>0$ be their minimum angular separation, in radians. The choices may be loose: these quantities need not equal the actual spectral gap.
--
--   Define $\Delta(j)=\Delta_2(j)$ when $j+2\le T$, $\Delta(j)=\Delta_1(j)$ when $j+1=T$, and $\Delta(T)=\Delta_0(T)$. Let $\check\Delta(j)=\min_{0\le i\le T,\ |i-j|\le1}\Delta(i)$. For nonnegative bounds $c_1(j),c_2(j)$, possibly dependent on $T$, suppose
--   $$
--   \|W_{j+1}-W_j\|\le\frac{c_1(j)}{T}\quad(j+1\le T),\qquad
--   \|W_{j+2}-2W_{j+1}+W_j\|\le\frac{c_2(j)}{T^2}\quad(j+2\le T).
--   $$
--   Set $\hat c_k(j)=\max\{c_k(i):0\le i,\ i+k\le T,\ |i-j|\le1\}$, with value zero if this set is empty, and assume $4\hat c_1(j)/\check\Delta(j)\le T$ at every grid index $j$.
--
--   Let $P_j$ be the spectral projection onto $\sigma_P(j)$ and $Q_j=I-P_j$. Construct $S_j=P_{j+1}P_j+Q_{j+1}Q_j$, $v_j=(S_jS_j^\dagger)^{1/2}$ and $V_j=v_j^{-1}S_j$. Define the chronological evolutions by $U_0=U_0^A=I$, $U_{j+1}=W_jU_j$, and $U_{j+1}^A=V_jW_jU_j^A$. Then for every integer $0\le n\le T$,
--   $$
--   \begin{aligned}
--   \|U_n-U_n^A\|\le{}&\frac{12\hat c_1(0)}{T\check\Delta(0)^2}
--   +\frac{12\hat c_1(n)}{T\check\Delta(n)^2}
--   +\frac{6\hat c_1(n)}{T\check\Delta(n)}\\
--   &+305\sum_{j=1}^{n-1}\frac{\hat c_1(j)^2}{T^2\check\Delta(j)^3}
--   +44\sum_{j=0}^{n-1}\frac{\hat c_1(j)^2}{T^2\check\Delta(j)^2}
--   +32\sum_{j=1}^{n-1}\frac{\hat c_2(j)}{T^2\check\Delta(j)^2}.
--   \end{aligned}
--   $$
--   Here $\|\cdot\|$ is the full operator norm and empty sums equal zero. This quantitative discrete adiabatic estimate retains the dependence on the first two forward differences and the chosen angular gaps.
--
--   **Formalization Note** The frozen spectral-window structure encodes compatible nested arc choices and $T\ge T_*$; spectral projections use continuous functional calculus. Finite ordinal intervals encode exactly the displayed integer summation ranges, including $n=0$ and $T=1$. The chronological product and neighboring minimum follow the proof's conventions where the introductory indexing and the appendix's word “maximum” are misprinted.
-- source:
--   Optimal scaling quantum linear systems solver via discrete adiabatic theorem, arXiv:2111.08152v1, Theorem 3, Section II.B, Eq. (15), PDF p. 6. https://arxiv.org/abs/2111.08152v1 . PDF SHA-256: e5837678c1edb2a45328aff275b18cfc7ef8c5c55d6248d5fe9346182e8f9af1.

import Definitions.Def_QAlgorithms_Defs_DiscreteAdiabaticTransport
set_option autoImplicit false

noncomputable section

namespace QAlgorithms.Papers.RoadmapA18

open scoped NNReal

open QAlgorithms.DiscreteAdiabatic

/-- Costa, An, Sanders, Su, Babbush and Berry, arXiv:2111.08152v1,
PDF p.6 (printed p.6), Theorem 3, Eq. (15): the Second Discrete Adiabatic Theorem.
Definitions 1--2 and Eqs. (21)--(26) supply the finite differences, compatible
spectral arc windows and left polar transport. The chronological product starts
with W(0), correcting the lower index of Eq. (2) and the shifted W in Eq. (3)
as required by Theorem 15 (p.14) and its proof (p.15, Eq. (86)).
The gap adjustment is the minimum in Eq. (14), correcting the appendix's word
"maximum" (p.30). The norm is the full operator norm on a complete complex
Hilbert space. No finite-dimensional or initial-state restriction is imposed. -/
theorem secondDiscreteAdiabaticTheorem
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {T : ℕ} (D : SpectralBandData H T)
    (c1 c2 : Fin (T + 1) → ℝ≥0)
    (firstDifference : ∀ (j : Fin (T + 1)) (valid : j.val + 1 ≤ T),
      ‖forwardDifference D.W 1 j.val valid‖ ≤ (c1 j : ℝ) / (T : ℝ))
    (secondDifference : ∀ (j : Fin (T + 1)) (valid : j.val + 2 ≤ T),
      ‖forwardDifference D.W 2 j.val valid‖ ≤ (c2 j : ℝ) / (T : ℝ) ^ 2)
    (positiveGaps : ∀ (j : Fin (T + 1)) (k : Fin 3) (valid : j.val + k.val ≤ T),
      0 < windowGap D j k valid)
    (stepSize : ∀ j : Fin (T + 1),
      4 * neighborEnvelope 1 c1 j / neighborGap D j ≤ (T : ℝ))
    (n : Fin (T + 1)) :
    let cHat1 := neighborEnvelope 1 c1
    let cHat2 := neighborEnvelope 2 c2
    let gap := neighborGap D
    ‖walkEvolution D.W n - idealEvolution D n‖ ≤
      12 * cHat1 0 / ((T : ℝ) * gap 0 ^ 2) +
      12 * cHat1 n / ((T : ℝ) * gap n ^ 2) +
      6 * cHat1 n / ((T : ℝ) * gap n) +
      305 * (∑ j ∈ Finset.Ico (1 : Fin (T + 1)) n,
        cHat1 j ^ 2 / ((T : ℝ) ^ 2 * gap j ^ 3)) +
      44 * (∑ j ∈ Finset.Ico (0 : Fin (T + 1)) n,
        cHat1 j ^ 2 / ((T : ℝ) ^ 2 * gap j ^ 2)) +
      32 * (∑ j ∈ Finset.Ico (1 : Fin (T + 1)) n,
        cHat2 j / ((T : ℝ) ^ 2 * gap j ^ 2)) := by sorry

end QAlgorithms.Papers.RoadmapA18
