-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P63_smooth_log_global_robustness
-- name    : QAlgorithms.Papers.Independent.Intake100.P63.smooth_log_global_robustness
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:16:16.683005+00:00
-- url     : https://prove2.me/theorems/2420da24-46ba-4ccc-8501-d715e72b6562
-- title:
--   §II, unnumbered: regularized relative entropy as smooth log global robustness
-- statement:
--   Let there be finitely many, at least one, parties with nonzero finite-dimensional local spaces $H_j$, and let $\rho\in\mathcal D(H_1\otimes\cdots\otimes H_k)$. At blocklength $n\ge1$, let $S_n$ consist of all finite convex combinations of products of normalized states on the grouped local blocks $H_j^{\otimes n}$. Local states may correlate a party's copies. Write $E_R^\infty(\rho)=\inf_{n\ge1}\inf_{\omega\in S_n}D_2(\rho^{\otimes n}\Vert\omega)/n$, with base-two relative entropy and the support convention $D_2=+\infty$ when support inclusion fails.
--
--   For normalized $\xi$, let $LR_{S_n}(\xi)=\inf_{\omega\in S_n}\inf\{s:\xi\le2^s\omega\}$, the log global robustness, and let $LR_{S_n}^\epsilon$ minimize this quantity over the closed full trace-norm $\epsilon$-ball of normalized states. Then
--   $$
--   \lim_{\epsilon\downarrow0}\liminf_{n\to\infty}\frac{LR_{S_n}^\epsilon(\rho^{\otimes n})}{n}
--   =E_R^\infty(\rho)
--   =\lim_{\epsilon\downarrow0}\limsup_{n\to\infty}\frac{LR_{S_n}^\epsilon(\rho^{\otimes n})}{n}.
--   $$
--
--   This relates distinguishability from classical correlations to robustness under mixing with unrestricted noise, rather than standard robustness with separable noise.
-- source:
--   A Generalization of Quantum Stein's Lemma, arXiv:0904.0281v3, PDF p. 6, §II, unnumbered: regularized relative entropy as smooth log global robustness

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P63

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P63

open QAlgorithms Filter Topology

open QAlgorithms.Papers.Independent.Information100.P60 (Mat relativeBits)

open QAlgorithms.Papers.Independent.Information100.P07 (positivePart)

open QAlgorithms.Papers.Independent.Information100.P21 (Vec)

open QAlgorithms.Papers.Independent.Gap48.P20 (Copies)

open QAlgorithms.Papers.Independent.Advance50.P30 (joinCopies defectTensor)

open QAlgorithms.Papers.Independent.Information100.P69 (permute)

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.6 after Eq.(16): smooth asymptotic log GLOBAL robustness.
By Eq.(7) this is max-relative entropy to separable states, with unrestricted noise. -/
theorem smooth_log_global_robustness {P : Type} [Fintype P] [DecidableEq P] [Nonempty P]
    (d : P → ℕ) (hd : ∀ j, 0 < d j)
    (rho : Mat (PartyReg d)) (hrho : IsDensityMatrix rho) :
    SmoothFormula (separableFamily d) rho := by sorry

end QAlgorithms.Papers.Independent.Intake100.P63

end
