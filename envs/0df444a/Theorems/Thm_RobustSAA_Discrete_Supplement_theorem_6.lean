-- Prove2me | Theorems.Thm_RobustSAA_Discrete_Supplement_theorem_6
-- name    : RobustSAA.Discrete.Supplement.theorem_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T19:41:58.988737+00:00
-- url     : https://prove2.me/theorems/e71a96e5-c194-4f7c-a3d8-cece470c752e
-- title:
--   Theorem 6 — the LCX-based test is consistent (null laws with finite second moment)
-- statement:
--   Let $\Xi\subseteq\mathbb R^d$ be closed and let $Q_C(N)=Q_{C_N}(\alpha_1)$ and $Q_R(N)=Q_{R_N}(\alpha_2)$ be threshold sequences with $Q_C(N)\to0$ and $Q_R(N)\to0$. Consider the LCX-based test (16), which rejects $F_0$ when $F_0\notin\mathcal F^{\alpha_1,\alpha_2}_{C_N,R_N}$, the region (17). Then for every data-generating law $F$ on $\Xi$ and every law $F_0\ne F$ on $\Xi$ with $\mathbb E_{F_0}[\|\xi\|_2^2]<\infty$,
--
--   $$\lim_{N\to\infty}\mathbb P\big(F_0\in\mathcal F^{\alpha_1,\alpha_2}_{C_N,R_N}(\xi^1,\dots,\xi^N)\big)=0,$$
--
--   where $\xi^1,\xi^2,\dots$ are iid from $F$; equivalently the probability of rejecting $F_0$ tends to $1$. The support may be unbounded.
--
--   The LCX test is the paper's multivariate goodness-of-fit test; consistency is the property that every fixed alternative is eventually detected.
--
--   Differences from the source:
--   - reading: the LCX-based test → the test (16)/(17) for arbitrary threshold sequences Q_C(N) → 0 and Q_R(N) → 0; reason: §10.10 uses only these limits (p. 40); the significance level plays no role
--   - correction: consistent: every F₀ ≠ F is rejected with probability → 1 → every F₀ ≠ F with E_{F₀}‖ξ‖₂² < ∞, every data-generating F; reason: (14) and §10.10 invoke Theorem 1 of [43], which assumes a finite second moment of F₀; counterexample in DISPROOF.md: for F₀ with infinite second moment and F a mean-preserving spread of F₀, the second-moment test never rejects and C_N(F₀) ≤ sup(E_F − Ê_N) stays below a suitably slowly vanishing Q_C with probability → 1; excluded: null laws with infinite second moment
--   - encoding: probability of rejection → 1 → outer probability of acceptance → 0; reason: equivalent for measurable events and stronger otherwise; no measurability presupposed
--   - encoding: E_{F₀} of hinges and of ‖ξ‖₂² → lower integrals in [0,∞]; C_N in EReal; reason: infinite expectations are represented, not defaulted to 0
-- source:
--   Bertsimas, Gupta, Kallus, Robust Sample Average Approximation, arXiv:1408.4445v3, Theorem 6, p. 15 (proof §10.10, p. 40)

import Mathlib
import Definitions.Def_RobustSAA_Convergence_Setting
import Definitions.Def_RobustSAA_Discrete_Supplement_LCX

namespace RobustSAA.Discrete.Supplement

open MeasureTheory Filter Topology RobustSAA.Convergence

theorem theorem_6 {d : ℕ} (Ξ : Set (Pt d)) (hΞ : IsClosed Ξ) (QC QR : ℕ → ℝ)
    (hQC : Tendsto QC atTop (𝓝 0)) (hQR : Tendsto QR atTop (𝓝 0)) :
    IsConsistentOn (fun F₀ : ProbabilityMeasure ↥Ξ => secondMoment F₀ < ⊤)
      (lcxDUS QC QR) := by sorry

end RobustSAA.Discrete.Supplement
