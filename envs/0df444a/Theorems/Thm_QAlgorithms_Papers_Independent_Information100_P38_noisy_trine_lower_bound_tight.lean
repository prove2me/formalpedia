-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P38_noisy_trine_lower_bound_tight
-- name    : QAlgorithms.Papers.Independent.Information100.P38.noisy_trine_lower_bound_tight
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T11:09:24.280513+00:00
-- url     : https://prove2.me/theorems/594419d0-54a7-447c-8ba8-4282fcb0de81
-- title:
--   Example 2
-- statement:
--   Let $H=E|1\rangle\langle1|$, $E>0$, and $0\le c\le1$. Set $M_\mu=(I+c\mathbf m_\mu\cdot\boldsymbol\sigma)/3$, where $\mathbf m_0=(1,0,0)$, $\mathbf m_1=(-1/2,\sqrt3/2,0)$ and $\mathbf m_2=(-1/2,-\sqrt3/2,0)$. These effects form a POVM with $C_{\ell_\infty}(M)=c$, and
--
--   $$A_H^M=\frac{Ec^2}{4}=\frac E4[C_{\ell_\infty}(M)]^2.$$
--
--   The endpoints are the three effects $I/3$ at $c=0$ and the rank-one trine at $c=1$. This family witnesses tightness of the qubit lower bound, without asserting equality for every qubit POVM.
-- source:
--   All coherent measurements provide observational ergotropic advantage, arXiv:2609.18735v1, PDF p. 8, Example 2

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P38

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P38

open scoped ComplexConjugate Matrix

/-- Paper pp.8–9, Example 2: the whole noisy-trine family attains the qubit lower
bound, including c=0 and c=1. -/
theorem noisy_trine_lower_bound_tight (E c : ℝ) (hE : 0 < E) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    IsPOVM (noisyErgotropicTrine c) ∧ measurementLinfCoherence (noisyErgotropicTrine c) = c ∧
    observationalAdvantage ![0, E] (noisyErgotropicTrine c) = E * c^2 / 4 ∧
    observationalAdvantage ![0, E] (noisyErgotropicTrine c) =
      E / 4 * (measurementLinfCoherence (noisyErgotropicTrine c))^2 := by sorry

end QAlgorithms.Papers.Independent.Information100.P38

end
