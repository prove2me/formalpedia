-- Prove2me | Theorems.Thm_SelfStructIS_LogEff_theorem_4_1
-- name    : SelfStructIS.LogEff.theorem_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T23:30:07.963965+00:00
-- url     : https://prove2.me/theorems/4fed5885-5ea0-4024-8db7-711a6b446951
-- title:
--   Theorem 4.1, p. 12 — log P(L(X) ≥ u) = −Λ_min(u^{1/ρ})[I* + o(1)]
-- statement:
--   Let $X$ satisfy Assumption 3.1 with indices $\alpha$, and suppose the standardized vector $Y=\Lambda(X)$ satisfies the tail LDP of Theorem 3.1: $\{Y/t\}$ obeys the large deviations principle with speed $t$ and a rate $I$ (extended by $+\infty$ off $\mathbb R^d_+$) that is continuous on $\mathbb R^d_+\setminus\{0\}$. Suppose the limit $q^*=\lim_{t\to\infty}\hat q(t)$ exists. Then for every measurable $L$ satisfying Assumption 2.1,
--   $$\log P(L(X)\ge u)=-\Lambda_{\min}(u^{1/\rho})\big[I^*+o(1)\big]\quad(u\to\infty),\qquad I^*=\inf\{I(y): L^*(q^*y^{1/\alpha})\ge1,\ y\ge0\},$$
--   that is, $\log P(L(X)\ge u)/t(u)\to -I^*$ with $t(u)=\Lambda_{\min}(u^{1/\rho})$.
--
--   This is the paper's large-deviations characterization of the target probability $p_u$, valid for nonconvex losses and nonparametric dependence; it is also the yardstick against which logarithmic efficiency (Theorem 5.1) is measured.
--
--   **Formalization Note** The limit is stated in `EReal` with $\log 0=-\infty$, so the case $I^*=+\infty$ (empty constraint set) reads $\log p_u/t(u)\to-\infty$ rather than producing a junk value. Measurability of $L$ is the standing convention implicit in $P(L(X)\ge u)$. The LDP is real-indexed, as in Theorem 3.1 of this mission. Continuity of $I$ on $\mathbb R^d_+\setminus\{0\}$ is part of the hypothesis: the page assumes "the tail LDP in Theorem 3.1", whose rate is continuous by Lemma 3.2(a), and the proof (p. 30, "Observe that $I(\cdot)$ and $L^*(\cdot)$ are continuous") uses it in (41a)–(41b). An LDP hypothesis alone does not determine $I$ off its lower-semicontinuous envelope, so it is stated explicitly; the value $I(0)$, which (13) leaves free, is not involved.
-- source:
--   Deo, Murthy, Achieving Efficiency in Black-Box Simulation of Distribution Tails with Self-Structuring Importance Samplers, arXiv:2102.07060v3, p. 12, Theorem 4.1, (15), (16) (proof pp. 28–31, App. A.1)

import Mathlib
import Definitions.Def_HeavyTailNV_Tail_Model
import Definitions.Def_SelfStructIS_LogEff_Setting
import Definitions.Def_SelfStructIS_LogEff_Sampler
import Definitions.Def_SelfStructIS_LogEff_Tail

open MeasureTheory Filter Topology

namespace SelfStructIS.LogEff

theorem theorem_4_1 (d : ℕ) (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    (α : Fin d → ℝ) (h31 : Assumption31 μ α)
    (I : (Fin d → ℝ) → ℝ) (hIcont : ContinuousOn I {y | (∀ i, 0 ≤ y i) ∧ y ≠ 0})
    (hLDP : IsLDP (fun t : ℝ => (μ.map (hazardVec μ)).map (fun y => t⁻¹ • y)) (rateExt I))
    (qstar : Fin d → ℝ) (hqstar : Tendsto (qhat μ) atTop (𝓝 qstar))
    (L Lstar : (Fin d → ℝ) → ℝ) (ρ : ℝ) (hL : Measurable L) (h21 : Assumption21 μ L ρ Lstar) :
    Tendsto (fun u : ℝ => (((tfun μ ρ u)⁻¹ : ℝ) : EReal) * ENNReal.log (μ {x | u ≤ L x}))
      atTop (𝓝 (-Istar Lstar qstar α I)) := by sorry

end SelfStructIS.LogEff
