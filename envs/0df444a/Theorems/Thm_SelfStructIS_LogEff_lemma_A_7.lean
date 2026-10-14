-- Prove2me | Theorems.Thm_SelfStructIS_LogEff_lemma_A_7
-- name    : SelfStructIS.LogEff.lemma_A_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T23:30:33.109639+00:00
-- url     : https://prove2.me/theorems/c2f4e073-03a9-47e8-9e94-7714e4bb4017
-- title:
--   Lemma A.7, p. 34 — aᵤ(p) ≥ I(p) + o(1) uniformly on compacts of ℝᵈ₊₊
-- statement:
--   Suppose $X$ (in $\mathbb R^d$, $d\ge1$) satisfies Assumptions 3.1–3.2, with $f_Y=p\,e^{-\varphi}$ and limiting function $I$; let $\rho>0$ and let $l=l(u)$ be slowly varying with $l(u)\to\infty$. Let $a_u$ be built with the exponent $\kappa^{(1)}$. Then
--   $$a_u(p)\ge I(p)+o(1)\qquad(u\to\infty),$$
--   uniformly over $p$ in compact subsets of $\mathbb R^d_{++}$: for every compact $K\subseteq\mathbb R^d_{++}$ and $\varepsilon>0$, for all sufficiently large $u$ and all $p\in K$, $a_u(p)\ge I(p)-\varepsilon$.
--
--   This is the lower bound on the density part of the exponent in Lemma A.6.
--
--   **Formalization Note** The proof uses (48), which needs $l(u)\to\infty$ (the hypothesis of Lemma A.5); it is added. $d\ge1$ is the paper's setting (at $d=0$ the value $I(0)$ is unconstrained).
-- source:
--   Deo, Murthy, Achieving Efficiency in Black-Box Simulation of Distribution Tails with Self-Structuring Importance Samplers, arXiv:2102.07060v3, p. 34, Lemma A.7

import Mathlib
import Definitions.Def_HeavyTailNV_Tail_Model
import Definitions.Def_SelfStructIS_LogEff_Setting
import Definitions.Def_SelfStructIS_LogEff_Sampler
import Definitions.Def_SelfStructIS_LogEff_Tail

open MeasureTheory Filter Topology

namespace SelfStructIS.LogEff

theorem lemma_A_7 (d : ℕ) (hd : 0 < d) (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    (α : Fin d → ℝ) (h31 : Assumption31 μ α)
    (p φ I : (Fin d → ℝ) → ℝ) (h32 : Assumption32 μ p φ I)
    (ρ : ℝ) (hρ : 0 < ρ)
    (l : ℝ → ℝ) (hl_sv : SlowlyVarying l) (hl_top : Tendsto l atTop atTop) :
    ∀ K : Set (Fin d → ℝ), IsCompact K → K ⊆ {q | ∀ i, 0 < q i} →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ u in atTop, ∀ q ∈ K,
        I q - ε ≤ aU μ (fun y => p y * Real.exp (-φ y)) .one ρ u (l u) q := by sorry

end SelfStructIS.LogEff
