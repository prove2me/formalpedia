-- Prove2me | Theorems.Thm_SelfStructIS_LogEff_lemma_A_5
-- name    : SelfStructIS.LogEff.lemma_A_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T23:30:25.308809+00:00
-- url     : https://prove2.me/theorems/23bc7c34-2ff7-4b8d-aed0-1cbe98a3232a
-- title:
--   Lemma A.5, p. 32 — ‖ψᵤ(t(u)p)‖∞ = o(t(u)) uniformly on compacts of ℝᵈ₊₊
-- statement:
--   Suppose $X$ satisfies Assumptions 3.1–3.2, $\rho>0$, and the hyper-parameter $l=l(u)$ is slowly varying with $l(u)\to\infty$. Let $T$ use the exponent $\kappa^{(1)}$ and let $\psi_u=\Lambda\circ T^{-1}\circ q$. Then, uniformly over $p$ in compact subsets of $\mathbb R^d_{++}$,
--   $$\|\psi_u(t(u)p)\|_\infty=o(t(u))\qquad(u\to\infty):$$
--   for every compact $K\subseteq\mathbb R^d_{++}$ and every $\varepsilon>0$, for all sufficiently large $u$ and all $p\in K$, $\|\psi_u(t(u)p)\|_\infty\le\varepsilon\,t(u)$.
--
--   The lemma says the sampler pulls the rare region back to points whose standardized size is negligible on the large-deviations scale.
--
--   **Formalization Note** $\psi_u(t(u)p)=\Lambda(x)$ for the preimage $x$ with $T(x)=q(t(u)p)$; the bound is stated for every such $x$. The printed "for any $\gamma>0$" binds no variable and is dropped.
-- source:
--   Deo, Murthy, Achieving Efficiency in Black-Box Simulation of Distribution Tails with Self-Structuring Importance Samplers, arXiv:2102.07060v3, p. 32, Lemma A.5 (proof pp. 32–33)

import Mathlib
import Definitions.Def_HeavyTailNV_Tail_Model
import Definitions.Def_SelfStructIS_LogEff_Setting
import Definitions.Def_SelfStructIS_LogEff_Sampler
import Definitions.Def_SelfStructIS_LogEff_Tail

open MeasureTheory Filter Topology

namespace SelfStructIS.LogEff

theorem lemma_A_5 (d : ℕ) (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    (α : Fin d → ℝ) (h31 : Assumption31 μ α)
    (p φ I : (Fin d → ℝ) → ℝ) (h32 : Assumption32 μ p φ I)
    (ρ : ℝ) (hρ : 0 < ρ)
    (l : ℝ → ℝ) (hl_sv : SlowlyVarying l) (hl_top : Tendsto l atTop atTop) :
    ∀ K : Set (Fin d → ℝ), IsCompact K → K ⊆ {q | ∀ i, 0 < q i} →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ u in atTop, ∀ q ∈ K, ∀ x : Fin d → ℝ,
        Tmap .one ρ u (l u) x = qvec μ (tfun μ ρ u • q) →
          ‖hazardVec μ x‖ ≤ ε * tfun μ ρ u := by sorry

end SelfStructIS.LogEff
