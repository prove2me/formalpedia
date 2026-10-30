-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P15_covariant_channel_comparison
-- name    : QAlgorithms.Papers.Independent.Extend50.P15.covariant_channel_comparison
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:55:24.991984+00:00
-- url     : https://prove2.me/theorems/bce7d6ce-a9df-4550-a344-29dc8a51b0a9
-- title:
--   Error comparison for two fully covariant channels
-- statement:
--   Let $\mathcal A$ and $\mathcal B$ be CPTP maps on $\mathbb C^d$, where $d\ge2$, and assume both commute with conjugation by every $U\in\mathrm{SU}(d)$. Let $\epsilon_{\mathrm{ent}}$ be half the trace distance between normalized Choi states, $F_{\mathrm{ent}}$ their squared Uhlmann fidelity, and $\epsilon_{\mathrm{wc}}$ half the diamond norm. If $\epsilon_{\mathrm{ent}}(\mathcal A,\mathcal B)\le1/2$, then
--
--   $$\epsilon_{\mathrm{wc}}(\mathcal B,\mathcal I)\le9d\max\{\epsilon_{\mathrm{ent}}(\mathcal A,\mathcal I),\ 1-F_{\mathrm{ent}}(\mathcal A,\mathcal B)\}.$$
--
--   The boundary value $1/2$ is included. This relates operational worst-case recovery error to quantities on normalized Choi states.
-- source:
--   Optimal Universal Quantum Error Correction via Bounded Reference Frames, arXiv:2007.09154v2, PDF p. 18, Lemma 5, A59

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P15

noncomputable section

open MeasureTheory

open scoped Matrix ComplexConjugate Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Extend50.P15

open QAlgorithms.Papers.Independent.Information100.P67 (squaredFidelity)

open QAlgorithms.Papers.Independent.Information100.P56 (normalizedChoi)

open QAlgorithms.Papers.Independent.Information100.P75 (Register)

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- Lemma 5, A59, PDF pp.18--19. Both channels are fully SU(d)-covariant; equality
in the hypothesis at 1/2 is allowed. -/
theorem covariant_channel_comparison (d : ℕ) (hd : 2 ≤ d)
    (A B : Superop (Fin d) (Fin d)) (hA : IsChannel A) (hB : IsChannel B)
    (hAcov : IsSUChannelCovariant A) (hBcov : IsSUChannelCovariant B)
    (hclose : entanglementError d (by omega) A B ≤ 1 / 2) :
    stabilizedHalfDiamondError B id ≤ 9 * d * max (entanglementError d (by omega) A id)
      (1 - choiPairFidelity d (by omega) A B) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P15

end
