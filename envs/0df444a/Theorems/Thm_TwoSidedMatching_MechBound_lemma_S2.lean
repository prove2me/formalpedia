-- Prove2me | Theorems.Thm_TwoSidedMatching_MechBound_lemma_S2
-- name    : TwoSidedMatching.MechBound.lemma_S2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T11:05:43.490439+00:00
-- url     : https://prove2.me/theorems/fd5b175e-5093-4b82-9e96-21329e09cb8a
-- title:
--   Lemma S.2, Suppl. Note p. 1 — expected buyer payments are at most expected buyer virtual surplus net of waiting
-- statement:
--   Let $y$ be a feasible, well-defined two-sided direct mechanism that satisfies (ICd′) and (IRd). Then
--
--   $$E\Big[\sum_{\phi\in H^T}p_\phi\Big]\le E\Big[\sum_{\phi\in H^T}V^d(v_\phi)\,m_\phi-b\,(s_\phi-t_\phi)\Big],$$
--
--   where $H^T$ is the realized buyer population, every agent reports truthfully, $V^d(v)=v-\bar F^d(v)/f^d(v)$ is the buyer virtual value, and the right-hand side is a finite expectation (its integrand is integrable).
--
--   This is the buyer half of the Myersonian bound on the intermediary's revenue: it replaces payments by virtual values, which is what makes the clairvoyant assignment value $\bar J(H^T)$ an upper bound on any incentive-compatible mechanism.
--
--   **Formalization Note.** Standing hypotheses as in Lemma S.1. The integrability of the right-hand side is stated as part of the conclusion so that the expectation is a genuine finite number.
-- source:
--   Chen and Hu, Pricing and Matching with Forward-looking Buyers and Sellers, submitted manuscript (SSRN 2859864, TSpace copy), Supplemental Note p. 1, Lemma S.2

import Mathlib
import Definitions.Def_TwoSidedMatching_MechBound_Mechanism

open MeasureTheory MechanismDesign.BilateralTrade

namespace TwoSidedMatching.MechBound

/-- Lemma S.2 (Supplemental Note p. 1): under (ICd′) and (IRd),
`E[Σ_{φ ∈ H^T} p_φ] ≤ E[Σ_{φ ∈ H^T} V^d(v_φ) m_φ − b (s_φ − t_φ)]`; the right-hand side is
integrable. -/
theorem lemma_S2
    (E : Environment)
    (hfB : ContinuousOn E.fB (Set.Icc E.loB E.hiB))
    (hfS : ContinuousOn E.fS (Set.Icc E.loS E.hiS))
    (hreg : E.Regular) (hcv : E.loS ≤ E.hiB)
    (lamD lamS T b h : ℝ) (hlamD : 0 < lamD) (hlamS : 0 < lamS) (hT : 0 < T)
    (hb : 0 ≤ b) (hh : 0 ≤ h)
    (y : Mechanism) (hfeas : Feasible E T y) (hwd : WellDefined E lamD lamS T y)
    (hIC : ICd' E lamD lamS T b y) (hIR : IRd E lamD lamS T b y) :
    Integrable (fun ω => ((Hd ω).map (fun φ =>
        E.psiB φ.2 * ((y (Hd ω) (Hs ω)).1 φ).m - b * (((y (Hd ω) (Hs ω)).1 φ).s - φ.1))).sum)
      (P E lamD lamS T) ∧
    ∫ ω, ((Hd ω).map (fun φ => ((y (Hd ω) (Hs ω)).1 φ).p)).sum ∂P E lamD lamS T ≤
      ∫ ω, ((Hd ω).map (fun φ =>
        E.psiB φ.2 * ((y (Hd ω) (Hs ω)).1 φ).m - b * (((y (Hd ω) (Hs ω)).1 φ).s - φ.1))).sum
        ∂P E lamD lamS T := by sorry

end TwoSidedMatching.MechBound
