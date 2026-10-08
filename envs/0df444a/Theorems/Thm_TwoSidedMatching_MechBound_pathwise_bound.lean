-- Prove2me | Theorems.Thm_TwoSidedMatching_MechBound_pathwise_bound
-- name    : TwoSidedMatching.MechBound.pathwise_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T11:05:47.474059+00:00
-- url     : https://prove2.me/theorems/cd6ace64-f7a2-49d1-ada7-c5b7926c8555
-- title:
--   Online Appendix p. 4, proof of Lemma 1 — J̄² ≤ E[J̄(H^T)]: balanced outcomes earn at most the assignment value (B)
-- statement:
--   Let $D$ be a finite multiset of buyer types in $[0,T]\times[\underline v,\bar v]$ and $S$ a finite multiset of seller types in $[0,T]\times[\underline c,\bar c]$, and assign to every buyer $\phi\in D$ an outcome $(s_\phi,m_\phi)$ and to every seller $\psi\in S$ an outcome $(s_\psi,m_\psi)$ with $t\le s\le T$ and $m\in\{0,1\}$, such that at every instant $t\in[0,T]$ the number of buyers discharged at $t$ with $m=1$ equals the number of such sellers. If $b,h\ge0$, then
--
--   $$\sum_{\phi\in D}\big(V^d(v_\phi)m_\phi-b(s_\phi-t_\phi)\big)-\sum_{\psi\in S}\big(V^s(c_\psi)m_\psi+h(s_\psi-t_\psi)\big)\le\bar J(D,S),$$
--
--   where $\bar J(D,S)$ is the optimal value of the clairvoyant assignment problem (B) on the profile $(D,S)$, with coefficients $V^d(v_\phi)-V^s(c_\psi)-b(t_\psi-t_\phi)^+-h(t_\phi-t_\psi)^+$.
--
--   This is the deterministic step of the proof of Lemma 1: a buyer and a seller who are matched leave together, no earlier than the later of their two arrivals, so their waiting costs are at least those charged in (B), and unmatched agents only lose. Taking expectations gives $\bar J^2\le E[\bar J(H^T)]$.
--
--   **Formalization Note.** Standing hypotheses of §3 are carried for uniformity. The statement is pathwise, for every profile, so the expectation version follows by integrating.
-- source:
--   Chen and Hu, Pricing and Matching with Forward-looking Buyers and Sellers, submitted manuscript (SSRN 2859864, TSpace copy), Online Appendix p. 4, proof of Lemma 1, the step J̄² ≤ E[J̄(H^T)]; problem (B), main text p. 14

import Mathlib
import Definitions.Def_TwoSidedMatching_MechBound_Mechanism

open MeasureTheory MechanismDesign.BilateralTrade

namespace TwoSidedMatching.MechBound

/-- The pathwise step `J̄² ≤ E[J̄(H^T)]` (Online Appendix p. 4): for every finite profile of buyer
and seller types and every assignment of outcomes with `t ≤ s ≤ T`, `m ∈ {0, 1}` and the
balancing condition (1),
`Σ_φ (V^d(v_φ) m_φ − b (s_φ − t_φ)) − Σ_ψ (V^s(c_ψ) m_ψ + h (s_ψ − t_ψ)) ≤ J̄` of the profile. -/
theorem pathwise_bound
    (E : Environment)
    (hfB : ContinuousOn E.fB (Set.Icc E.loB E.hiB))
    (hfS : ContinuousOn E.fS (Set.Icc E.loS E.hiS))
    (hreg : E.Regular) (hcv : E.loS ≤ E.hiB)
    (lamD lamS T b h : ℝ) (hlamD : 0 < lamD) (hlamS : 0 < lamS) (hT : 0 < T)
    (hb : 0 ≤ b) (hh : 0 ≤ h)
    (D S : Multiset (ℝ × ℝ)) (oD oS : ℝ × ℝ → Outcome)
    (hD : ∀ φ ∈ D, φ ∈ buyerTypes E T) (hS : ∀ ψ ∈ S, ψ ∈ sellerTypes E T)
    (hoD : ∀ φ ∈ D, AgentFeasible T φ (oD φ)) (hoS : ∀ ψ ∈ S, AgentFeasible T ψ (oS ψ))
    (hbal : Balanced T D S oD oS) :
    (D.map (fun φ => E.psiB φ.2 * (oD φ).m - b * ((oD φ).s - φ.1))).sum -
        (S.map (fun ψ => E.psiS ψ.2 * (oS ψ).m + h * ((oS ψ).s - ψ.1))).sum ≤
      JbarProfile E b h D S := by sorry

end TwoSidedMatching.MechBound
