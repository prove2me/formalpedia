-- Prove2me | Theorems.Thm_TwoSidedMatching_MechBound_lemma_1_mechanism_bound
-- name    : TwoSidedMatching.MechBound.lemma_1_mechanism_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T11:05:31.571413+00:00
-- url     : https://prove2.me/theorems/6fefe061-6a71-4283-95e5-e5cd436116d2
-- title:
--   Online Appendix p. 4, proof of Lemma 1 — J* ≤ E[J̄(H^T)]: no incentive-compatible two-sided mechanism beats the expected virtual-surplus assignment value
-- statement:
--   Consider the two-sided market of Chen and Hu: over $[0,T]$ buyers with types $\phi=(t_\phi,v_\phi)$ arrive as a Poisson process of rate $\lambda^d$ with valuations of continuous positive density $f^d$ on $[\underline v,\bar v]$, and sellers with types $\psi=(t_\psi,c_\psi)$ arrive as an independent Poisson process of rate $\lambda^s$ with costs of continuous positive density $f^s$ on $[\underline c,\bar c]$; the virtual value $V^d$ and virtual cost $V^s$ are increasing (Assumptions 1–2), $\underline c\le\bar v$, and the waiting costs satisfy $b,h\ge0$.
--
--   Let $y$ be a feasible, well-defined two-sided direct mechanism (every agent discharged at a time $s\in[t,T]$ with $m\in\{0,1\}$, and the balancing condition holds at every instant) that satisfies the incentive constraints (ICd), (ICs) and the participation constraints (IRd), (IRs) of problem (B′). Then $\bar J(H^T)$ is integrable and
--
--   $$E\big[\Pi(y^T)\big]\le E\big[\bar J(H^T)\big],$$
--
--   where $\Pi(y^T)=\sum_{\phi\in H^T}p_\phi-\sum_{\psi\in H^T}p_\psi$ is the intermediary's profit and $\bar J(H^T)$ is the optimal value of the clairvoyant assignment problem (B) with coefficients $V^d(v_\phi)-V^s(c_\psi)-b(t_\psi-t_\phi)^+-h(t_\phi-t_\psi)^+$.
--
--   Equivalently, the optimal value $J^*$ of (B′) satisfies $J^*\le E[\bar J(H^T)]$ — the chain $J^*\le\bar J^1\le\bar J^2\le E[\bar J(H^T)]$ that closes the proof of Lemma 1. Together with the revelation principle (Lemma 3, $J^{\pi,M}\le J^*$) it shows that no pricing and matching policy earns more than $E[\bar J(H^T)]$, the benchmark against which the paper measures its waiting-adjusted fixed-price policy.
--
--   **Formalization Note.** The statement quantifies over every admissible mechanism instead of taking a supremum; it is equivalent to $J^*\le E[\bar J(H^T)]$ because the null mechanism (discharge on arrival, no trade, no payment) is admissible. Mechanisms may depend on the whole reported profile: the paper's causality conditions are dropped, which enlarges the class, so the bound is stronger than the paper's. The interim expectation $E_{-\phi}$ is taken over an independent copy of the arrival process into which the agent's report is inserted (Slivnyak–Mecke). The continuity of the densities is an added standing hypothesis: without it $V^d$, $V^s$ are defined only almost everywhere.
-- source:
--   Chen and Hu, Pricing and Matching with Forward-looking Buyers and Sellers, submitted manuscript (SSRN 2859864, TSpace copy), Online Appendix p. 4, proof of Lemma 1, last display (J* ≤ J̄¹ ≤ J̄² ≤ E[J̄(H^T)]); J* defined Online Appendix p. 3, (B′) p. 2

import Mathlib
import Definitions.Def_TwoSidedMatching_MechBound_Mechanism

open MeasureTheory MechanismDesign.BilateralTrade

namespace TwoSidedMatching.MechBound

/-- Online Appendix p. 4, proof of Lemma 1: `J* ≤ J̄¹ ≤ J̄² ≤ E[J̄(H^T)]`. Every feasible,
well-defined two-sided direct mechanism satisfying (ICd), (IRd), (ICs), (IRs) of (B′) has
expected profit `E[Π(y^T)] ≤ E[J̄(H^T)]`, and `J̄(H^T)` is integrable. -/
theorem lemma_1_mechanism_bound
    (E : Environment)
    (hfB : ContinuousOn E.fB (Set.Icc E.loB E.hiB))
    (hfS : ContinuousOn E.fS (Set.Icc E.loS E.hiS))
    (hreg : E.Regular) (hcv : E.loS ≤ E.hiB)
    (lamD lamS T b h : ℝ) (hlamD : 0 < lamD) (hlamS : 0 < lamS) (hT : 0 < T)
    (hb : 0 ≤ b) (hh : 0 ≤ h)
    (y : Mechanism) (hfeas : Feasible E T y) (hwd : WellDefined E lamD lamS T y)
    (hICd : ICd E lamD lamS T b y) (hIRd : IRd E lamD lamS T b y)
    (hICs : ICs E lamD lamS T h y) (hIRs : IRs E lamD lamS T h y) :
    Integrable (Jbar E b h) (P E lamD lamS T) ∧
      ∫ ω, profit y ω ∂P E lamD lamS T ≤ ∫ ω, Jbar E b h ω ∂P E lamD lamS T := by sorry

end TwoSidedMatching.MechBound
