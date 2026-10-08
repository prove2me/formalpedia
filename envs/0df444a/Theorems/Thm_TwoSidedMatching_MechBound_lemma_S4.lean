-- Prove2me | Theorems.Thm_TwoSidedMatching_MechBound_lemma_S4
-- name    : TwoSidedMatching.MechBound.lemma_S4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T11:05:56.195973+00:00
-- url     : https://prove2.me/theorems/b251d807-3f8b-47d0-b909-b5768cbe4856
-- title:
--   Lemma S.4, Suppl. Note p. 3 — expected seller payments are at least expected seller virtual cost plus waiting
-- statement:
--   Let $y$ be a feasible, well-defined two-sided direct mechanism that satisfies (ICs′) and (IRs). Then
--
--   $$E\Big[\sum_{\psi\in H^T}p_\psi\Big]\ge E\Big[\sum_{\psi\in H^T}V^s(c_\psi)\,m_\psi+h\,(s_\psi-t_\psi)\Big],$$
--
--   where $H^T$ is the realized seller population, every agent reports truthfully, $V^s(c)=c+F^s(c)/f^s(c)$ is the seller virtual cost, and the right-hand side is a finite expectation (its integrand is integrable).
--
--   This is the seller half of the Myersonian bound: the intermediary's expected outlay to sellers is at least their expected virtual cost of the units delivered plus their waiting costs.
--
--   **Formalization Note.** Standing hypotheses as in Lemma S.1. The integrability of the right-hand side is part of the conclusion.
-- source:
--   Chen and Hu, Pricing and Matching with Forward-looking Buyers and Sellers, submitted manuscript (SSRN 2859864, TSpace copy), Supplemental Note p. 3, Lemma S.4

import Mathlib
import Definitions.Def_TwoSidedMatching_MechBound_Mechanism

open MeasureTheory MechanismDesign.BilateralTrade

namespace TwoSidedMatching.MechBound

/-- Lemma S.4 (Supplemental Note p. 3): under (ICs′) and (IRs),
`E[Σ_{ψ ∈ H^T} p_ψ] ≥ E[Σ_{ψ ∈ H^T} V^s(c_ψ) m_ψ + h (s_ψ − t_ψ)]`; the right-hand side is
integrable. -/
theorem lemma_S4
    (E : Environment)
    (hfB : ContinuousOn E.fB (Set.Icc E.loB E.hiB))
    (hfS : ContinuousOn E.fS (Set.Icc E.loS E.hiS))
    (hreg : E.Regular) (hcv : E.loS ≤ E.hiB)
    (lamD lamS T b h : ℝ) (hlamD : 0 < lamD) (hlamS : 0 < lamS) (hT : 0 < T)
    (hb : 0 ≤ b) (hh : 0 ≤ h)
    (y : Mechanism) (hfeas : Feasible E T y) (hwd : WellDefined E lamD lamS T y)
    (hIC : ICs' E lamD lamS T h y) (hIR : IRs E lamD lamS T h y) :
    Integrable (fun ω => ((Hs ω).map (fun ψ =>
        E.psiS ψ.2 * ((y (Hd ω) (Hs ω)).2 ψ).m + h * (((y (Hd ω) (Hs ω)).2 ψ).s - ψ.1))).sum)
      (P E lamD lamS T) ∧
    ∫ ω, ((Hs ω).map (fun ψ =>
        E.psiS ψ.2 * ((y (Hd ω) (Hs ω)).2 ψ).m + h * (((y (Hd ω) (Hs ω)).2 ψ).s - ψ.1))).sum
        ∂P E lamD lamS T ≤
      ∫ ω, ((Hs ω).map (fun ψ => ((y (Hd ω) (Hs ω)).2 ψ).p)).sum ∂P E lamD lamS T := by sorry

end TwoSidedMatching.MechBound
