-- Prove2me | Theorems.Thm_SelfStructIS_LogEff_lemma_A_1
-- name    : SelfStructIS.LogEff.lemma_A_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T23:30:18.875219+00:00
-- url     : https://prove2.me/theorems/fe81f4d9-e3e5-4e83-b737-d7086fff004f
-- title:
--   Lemma A.1, p. 28 — q_∞(t(u)) = u^{1/ρ}, and {L(X) ≥ u} = {Yᵤ ∈ lev⁺₁(Lᵤ)}
-- statement:
--   Let $X$ (in $\mathbb R^d$, $d\ge1$) satisfy Assumption 3.1, and let $\rho>0$. Then for all sufficiently large $u$,
--   $$q_\infty(t(u))=u^{1/\rho},\qquad t(u)=\Lambda_{\min}(u^{1/\rho}).$$
--   If moreover $L$ satisfies Assumption 2.1 with this $\rho$, then for all sufficiently large $u$ the events $\{L(X)\ge u\}$ and $\{Y_u\in\mathbb R^d_{++},\ L_u(Y_u)\ge1\}$, where $Y_u=\Lambda(X)/t(u)$ and $L_u(x)=u^{-1}L(q(t(u)x))$, have the same probability:
--   $$P(L(X)\ge u)=P\big(Y_u\in\mathbb R^d_{++},\ L_u(Y_u)\ge1\big).$$
--
--   The identity rewrites the rare event in the standardized coordinates in which the tail LDP operates.
--
--   **Formalization Note** The first claim needs $u^{1/\rho}>x_0$ (the paper assumes $u>x_0$ throughout App. A), hence "for all sufficiently large $u$". The paper says the events "coincide"; they coincide almost surely ($q\circ\Lambda$ is the identity off flat stretches of $\Lambda$, which carry no mass, and $Y>0$ a.s.), so equality of probabilities is stated. $\rho>0$ comes from Assumption 2.1 in the paper and is assumed explicitly for the first claim.
-- source:
--   Deo, Murthy, Achieving Efficiency in Black-Box Simulation of Distribution Tails with Self-Structuring Importance Samplers, arXiv:2102.07060v3, p. 28, Lemma A.1

import Mathlib
import Definitions.Def_HeavyTailNV_Tail_Model
import Definitions.Def_SelfStructIS_LogEff_Setting
import Definitions.Def_SelfStructIS_LogEff_Sampler
import Definitions.Def_SelfStructIS_LogEff_Tail

open MeasureTheory Filter Topology

namespace SelfStructIS.LogEff

theorem lemma_A_1 (d : ℕ) (hd : 0 < d) (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    (α : Fin d → ℝ) (h31 : Assumption31 μ α) (ρ : ℝ) (hρ : 0 < ρ) :
    (∀ᶠ u in atTop, qinfty μ (tfun μ ρ u) = u ^ (1 / ρ)) ∧
      ∀ L Lstar : (Fin d → ℝ) → ℝ, Assumption21 μ L ρ Lstar →
        ∀ᶠ u in atTop, μ {x | u ≤ L x} =
          μ {x | (∀ i, 0 < ((tfun μ ρ u)⁻¹ • hazardVec μ x) i) ∧
            1 ≤ Lu μ L ρ u ((tfun μ ρ u)⁻¹ • hazardVec μ x)} := by sorry

end SelfStructIS.LogEff
