-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P73_wiretap_one_shot
-- name    : QAlgorithms.Papers.Independent.Intake100.P73.wiretap_one_shot
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:53:40.227987+00:00
-- url     : https://prove2.me/theorems/5db6d113-1cd1-42fd-bfc0-bc8d1840a4ad
-- title:
--   Theorem 3: one code meets five reliability and secrecy bounds
-- statement:
--   Let $B:X\to\mathcal P(Y)$ and $E:X\to\mathcal P(Z)$ be classical discrete channels with a common input, and let $p\in\mathcal P(X)$. No degradedness assumption is imposed. Fix positive integers $L,M$ and independent threshold parameters $C,C'>0$. For a channel $V$ define $V_p=\sum_xp(x)V_x$, $\phi(t\mid V,p)=\log\sum_y(\sum_xp(x)V_x(y)^{1/(1+t)})^{1+t}$, $\delta_V=\mathbb P_{pV}\{V_x/V_p>C\}$, $\delta'_V=\sum_xp(x)\sum_{V_x/V_p\le C}V_x^2/V_p$, and $\eta(a)=-a\log a$, with null-support and zero-entropy terms treated by their usual conventions.
--
--   There is ONE stochastic wiretap code $\Phi$ of exactly $M$ equiprobable messages with pairwise disjoint Bob regions, for which
--   $$
--   \epsilon_B(\Phi)\le3\inf_{0\le s\le1}(ML)^s e^{\phi(s\mid B,p)},\qquad
--   \epsilon_B(\Phi)\le3\left(\mathbb P_{pB}\{B_x/B_p\le C'\}+ML/C'\right),
--   $$
--   $$
--   I_E(\Phi)\le3\inf_{-1/2\le t<0}\frac{\log(1+L^te^{\phi(t\mid E,p)})}{-t},\qquad
--   d_E(\Phi)\le6\left(2\delta_E+\sqrt{\delta'_E/L}\right).
--   $$
--   If $Z$ is finite, this same code additionally satisfies
--   $$
--   I_E(\Phi)\le3\left(\eta(\delta_E)+\delta_E\log|Z|+\delta'_E/L\right).
--   $$
--   Here $\epsilon_B$ is average Bob error, $I_E=M^{-1}\sum_i D(E_{Q_i}\|M^{-1}\sum_jE_{Q_j})$, and $d_E$ is average full L1 over ordered distinct message pairs, defined as zero for $M=1$. All logarithms are natural. The simultaneous guarantee controls the reliability and both secrecy criteria of one actual code.
-- source:
--   General non-asymptotic and asymptotic formulas in channel resolvability and identification capacity and their application to wire-tap channel, arXiv:cs/0503088v2, PDF p. 6, Theorem 3, (19)–(23): one wiretap code with reliability and secrecy bounds

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P73

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P73

open Filter

open scoped BigOperators ENNReal Topology

attribute [local instance] Classical.propDecidable Classical.decEq

universe u

/-- Hayashi, PDF pp.6–7, Theorem 3, (19)–(23): ONE code meets ALL five bounds.
Only (21) is conditional on finite Z. M=1 has empty pair-average leakage zero. -/
theorem wiretap_one_shot {X Y Z : Type*}
    (B : X → Y → ℝ≥0∞) (E : X → Z → ℝ≥0∞)
    (hB : IsDiscreteStochastic B) (hE : IsDiscreteStochastic E) (p : PMF X)
    (L M : ℕ) (hL : 0 < L) (hM : 0 < M) (C Cp : ℝ) (hC : 0 < C) (hCp : 0 < Cp) :
    ∃ c : DiscreteStochasticWiretapCode X Y, c.messages = M ∧
      (averageBobError B c : EReal) ≤ 3 * sInf
        ((fun s : ℝ => ((((M * L : ℕ) : ℝ≥0∞) ^ s * phiMoment B p s : ℝ≥0∞) : EReal)) '' Set.Icc 0 1) ∧
      averageBobError B c ≤ ENNReal.ofReal (3 * (lowTail B p Cp + ((M * L : ℕ) : ℝ) / Cp)) ∧
      (Finite Z → averageEveDivergence E c ≤ ENNReal.ofReal (3 * entropyBound E p L C)) ∧
      (averageEveDivergence E c : EReal) ≤ 3 * sInf
        ((fun t : ℝ => klBound E p L t) '' Set.Ico (-(1 / 2)) 0) ∧
      eveDistance E c ≤ ENNReal.ofReal (6 * l1Bound E p C L) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P73

end
