-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P89_process_firstChaos
-- name    : QAlgorithms.Papers.Independent.Intake100.P89.process_firstChaos
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:32:37.619673+00:00
-- url     : https://prove2.me/theorems/158dd3bd-0719-4c7e-9b02-49db3b543cac
-- title:
--   §2.1, unnumbered first-chaos representation
-- statement:
--   Let $W=(W_t)_{t\in T}$ be any centered real Gaussian process on a probability space $(\Omega,\mathcal U,P)$, including degenerate processes. Let $G$ be the closed real linear span of its coordinate classes in $L^2(P)$. Its covariance RKHS is precisely the functions $JH(t)=E[W_tH]$, $H\in G$, and
--   $$\langle JH_1,JH_2\rangle_H=E[H_1H_2],\qquad \|JH\|_H=\|H\|_2.$$
--   The representation is unique. Thus the completion embeds into actual functions on the arbitrary index set, with no sample-path regularity assumption.
-- source:
--   Reproducing kernel Hilbert spaces of Gaussian priors, arXiv:0805.3252v1, PDF p. 3, §2.1, unnumbered first-chaos representation

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P89

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory

open scoped Topology BigOperators ENNReal

namespace QAlgorithms.Papers.Independent.Intake100.P89

universe u v w

variable {Omega : Type u} [MeasurableSpace Omega]

section ProcessResults

variable (P : Measure Omega) [hP : IsProbabilityMeasure P]

include hP

/-- §2.1, unnumbered first-chaos representation, arXiv:0805.3252v1, PDF p.3.
The completion is realized by the closed L² span; injectivity of its function embedding and its induced inner product are conclusions. -/
theorem process_firstChaos
{T : Type v} (W : T → Omega → ℝ) (hW : CenteredProcess P W) :
    Function.Injective (fun h : processChaos P W => processSynthesis P W (h : L2 P)) ∧
    (∀ h : processChaos P W, processNorm P W (processSynthesis P W (h : L2 P)) = ‖h‖) ∧
    (∀ g h : processChaos P W,
      processInner P W (processSynthesis P W (g : L2 P))
        (processSynthesis P W (h : L2 P)) = inner ℝ g h) ∧
    processRKHS P W = Set.range (fun h : processChaos P W => processSynthesis P W (h : L2 P)) := by sorry

end ProcessResults

end QAlgorithms.Papers.Independent.Intake100.P89

end
