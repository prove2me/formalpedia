-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P44_amplifier_family_comparison
-- name    : QAlgorithms.Papers.Independent.Gap48.P44.amplifier_family_comparison
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T05:47:01.579818+00:00
-- url     : https://prove2.me/theorems/49c3937e-9561-4ca4-9c03-994f590ccf20
-- title:
--   Vacuum-amplifier families: gain ordering and time-sharing improvement
-- statement:
--   Write $g_n(x)=(x+1)\ln(x+1)-x\ln x$ and $g_b(x)=g_n(x)/\ln2$ for $x\ge0$, with $0\ln0=0$. Fix $N_S=200$ and $N_B=0$. For each finite gain $\kappa\ge1$, put $a_\kappa=g_b(200\kappa+\kappa-1)$, $b_\kappa(\lambda)=g_b(200\kappa\lambda+\kappa-1)$, and $e_\kappa(\lambda)=g_b((\kappa-1)(200\lambda+1))$. Let $A_{CQ}(\kappa)$ be the union of nonnegative $(C,Q)$ with $Q\le b_\kappa(\lambda)-e_\kappa(\lambda)$ and $C+Q\le a_\kappa-e_\kappa(\lambda)$. Let $A_{CE}(\kappa)$ be the union of nonnegative $(C,E_c)$ with $C\le g_b(200\lambda)+a_\kappa-e_\kappa(\lambda)$ and $C\le a_\kappa-e_\kappa(\lambda)+E_c$. Both unions use $\lambda\in[0,1]$. Then
--
--   $$1\le\kappa_1\le\kappa_2\ \Longrightarrow\ A_{CQ}(\kappa_2)\subseteq A_{CQ}(\kappa_1),\quad A_{CE}(\kappa_2)\subseteq A_{CE}(\kappa_1).$$
--
--   For every $\kappa>1$, the same-budget endpoint time-sharing families are properly contained in these respective families. Their endpoints are $C_0=a_\kappa-g_b(\kappa-1)$ and $Q_1=a_\kappa-g_b(201(\kappa-1))$ in CQ; CE uses $C_0$, $C_1=g_b(200)+Q_1$, and $E_1=g_b(200)$. CQ time sharing allows $C\le(1-t)C_0$, $Q\le tQ_1$; CE allows $C\le(1-t)C_0+tC_1$, $E_c\ge tE_1$, always with $t\in[0,1]$. At $\kappa=1$ each time-sharing family equals its corresponding coding family.
--
--   This is a comparison of the explicit inner families at the figure’s fixed budget, with consumed entanglement positive; it is not an identification of unrestricted amplifier capacity.
-- source:
--   Quantum trade-off coding for bosonic communication, arXiv:1105.0119v4, PDF p. 16, §V / Figure 6: amplification and time-sharing comparison

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P44

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P44

open Filter

open scoped ENNReal Topology

open QAlgorithms.Papers.Independent.Claimed50.P39 (g)

open QAlgorithms.Papers.Independent.Information100.P54 (thermalEntropy)

/-- PDF pp.16-17, Section V and Figure 6: ordered-gain inclusion of the
N_S=200,N_B=0 displayed families, plus proper time-sharing improvement at gain>1.
At identity gain the straight-line families equal endpoint time sharing. -/
theorem amplifier_family_comparison :
    (∀ k1 k2 : ℝ, 1 ≤ k1 → k1 ≤ k2 →
      amplifierCQ k2 ⊆ amplifierCQ k1 ∧ amplifierCE k2 ⊆ amplifierCE k1) ∧
    (∀ gain : ℝ, 1 < gain →
      cqTimeSharing
        (thermalEntropy (gain * 200 + gain - 1) - thermalEntropy (gain - 1))
        (thermalEntropy (gain * 200 + gain - 1) -
          thermalEntropy ((gain - 1) * 201)) ⊂ amplifierCQ gain ∧
      ceTimeSharing
        (thermalEntropy (gain * 200 + gain - 1) - thermalEntropy (gain - 1))
        (thermalEntropy 200 + thermalEntropy (gain * 200 + gain - 1) -
          thermalEntropy ((gain - 1) * 201)) (thermalEntropy 200) ⊂ amplifierCE gain) ∧
    cqTimeSharing (thermalEntropy 200) (thermalEntropy 200) = amplifierCQ 1 ∧
    ceTimeSharing (thermalEntropy 200) (2 * thermalEntropy 200) (thermalEntropy 200) =
      amplifierCE 1 := by sorry

end QAlgorithms.Papers.Independent.Gap48.P44

end
