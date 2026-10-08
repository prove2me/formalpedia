-- Prove2me | Theorems.Thm_TwoSidedMatching_MechBound_lemma_S1
-- name    : TwoSidedMatching.MechBound.lemma_S1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T11:05:35.347984+00:00
-- url     : https://prove2.me/theorems/3805fa36-3a0c-49ad-9c4c-d934b4ff307b
-- title:
--   Lemma S.1, Suppl. Note p. 1 — envelope bound on a buyer's interim expected payment
-- statement:
--   Let $y$ be a feasible, well-defined two-sided direct mechanism that satisfies the one-dimensional incentive constraints (ICd′) and the participation constraints (IRd) on the buyer side. Then for every buyer type $\phi=(t_\phi,v_\phi)\in[0,T]\times[\underline v,\bar v]$,
--
--   $$E_{-\phi}[p_\phi]\le v_\phi\,E_{-\phi}[m_\phi]-\int_{\underline v}^{v_\phi}E_{-\phi}\big[m_{\phi_{v'}}\big]\,dv'-b\,E_{-\phi}[s_\phi-t_\phi],$$
--
--   where $\phi_{v'}=(t_\phi,v')$ is the report that keeps the true arrival time and announces valuation $v'$, and $E_{-\phi}$ is the expectation over the other agents' arrivals and types. The integrand $v'\mapsto E_{-\phi}[m_{\phi_{v'}}]$ is integrable on $[\underline v,v_\phi]$, so the integral is a genuine one.
--
--   This is the Myersonian envelope bound for one agent: it caps the interim payment of a buyer by the surplus her allocation probability generates, less the information rent of the lower types. Integrated against the type distribution it yields Lemma S.2.
--
--   **Formalization Note.** The standing assumptions of the paper's §3 are hypotheses: continuous positive densities, Assumptions 1–2 (regularity of $V^d$, $V^s$), $\underline c\le\bar v$, positive rates and horizon, and $b,h\ge 0$. The interim expectation of the inserted report is taken under an independent copy of the arrival process (Slivnyak–Mecke).
-- source:
--   Chen and Hu, Pricing and Matching with Forward-looking Buyers and Sellers, submitted manuscript (SSRN 2859864, TSpace copy), Supplemental Note p. 1, Lemma S.1

import Mathlib
import Definitions.Def_TwoSidedMatching_MechBound_Mechanism

open MeasureTheory MechanismDesign.BilateralTrade

namespace TwoSidedMatching.MechBound

/-- Lemma S.1 (Supplemental Note p. 1): under (ICd′) and (IRd), for every buyer type
`φ = (t_φ, v_φ)`,
`E_{−φ}[p_φ] ≤ v_φ E_{−φ}[m_φ] − ∫_{v̲}^{v_φ} E_{−φ}[m_{φ_{v′}}] dv′ − b E_{−φ}[s_φ − t_φ]`;
the integrand `v′ ↦ E_{−φ}[m_{φ_{v′}}]` is interval integrable. -/
theorem lemma_S1
    (E : Environment)
    (hfB : ContinuousOn E.fB (Set.Icc E.loB E.hiB))
    (hfS : ContinuousOn E.fS (Set.Icc E.loS E.hiS))
    (hreg : E.Regular) (hcv : E.loS ≤ E.hiB)
    (lamD lamS T b h : ℝ) (hlamD : 0 < lamD) (hlamS : 0 < lamS) (hT : 0 < T)
    (hb : 0 ≤ b) (hh : 0 ≤ h)
    (y : Mechanism) (hfeas : Feasible E T y) (hwd : WellDefined E lamD lamS T y)
    (hIC : ICd' E lamD lamS T b y) (hIR : IRd E lamD lamS T b y) :
    ∀ φ ∈ buyerTypes E T,
      IntervalIntegrable (fun v' => Eminus E lamD lamS T y (φ.1, v') (fun o => o.m))
          volume E.loB φ.2 ∧
      Eminus E lamD lamS T y φ (fun o => o.p) ≤
        φ.2 * Eminus E lamD lamS T y φ (fun o => o.m) -
          (∫ v' in E.loB..φ.2, Eminus E lamD lamS T y (φ.1, v') (fun o => o.m)) -
          b * Eminus E lamD lamS T y φ (fun o => o.s - φ.1) := by sorry

end TwoSidedMatching.MechBound
