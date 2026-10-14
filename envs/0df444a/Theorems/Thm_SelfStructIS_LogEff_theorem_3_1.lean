-- Prove2me | Theorems.Thm_SelfStructIS_LogEff_theorem_3_1
-- name    : SelfStructIS.LogEff.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T23:30:20.049979+00:00
-- url     : https://prove2.me/theorems/69a74906-8ce5-403e-853e-ed696209d9a2
-- title:
--   Theorem 3.1, p. 11 — tail LDP for Y/t with rate I and speed t
-- statement:
--   Let $Y$ be a random vector in $\mathbb R^d$ ($d\ge1$) taking values in $\mathbb R^d_+$, with probability density
--   $$f_Y(y)=p(y)\exp(-\varphi(y)),$$
--   and let $I:\mathbb R^d_+\to\mathbb R_+$ be such that, for every sequence $y_n\to y\ne0$ in $\mathbb R^d_+$ and every $\varepsilon>0$, $n^{-1}\varphi(ny_n)\to I(y)$, $p(ny_n)>0$ for all large $n$, and $n^{-\varepsilon}\log p(ny_n)\to0$. Then the family $\{Y/t: t>0\}$ satisfies the large deviations principle with rate function $I$ (extended by $+\infty$ off $\mathbb R^d_+$) and speed $t$: for every closed $F$ and open $G$,
--   $$\limsup_{t\to\infty}\frac1t\log P\Big(\frac Yt\in F\Big)\le-\inf_{F}I,\qquad \liminf_{t\to\infty}\frac1t\log P\Big(\frac Yt\in G\Big)\ge-\inf_{G}I.$$
--
--   The tail LDP is what turns the nonparametric density assumption (12)–(13) into exponential rates for rare events; Theorem 4.1 applies it along the speed $t(u)$.
--
--   **Formalization Note** The theorem is printed for the sequence $\{n^{-1}Y\}$ with speed $n$; its proof ((35), p. 27) works with real $t\to\infty$, and Theorem 4.1 uses the LDP along the real speed $t(u)$, so the real-indexed form is stated (it implies the printed one). $Y\ge0$ is explicit because $I$ is only defined on $\mathbb R^d_+$, as for $Y=\Lambda(X)$. Probabilities are logged in `EReal`, so a zero probability gives $-\infty$.
-- source:
--   Deo, Murthy, Achieving Efficiency in Black-Box Simulation of Distribution Tails with Self-Structuring Importance Samplers, arXiv:2102.07060v3, p. 11, Theorem 3.1 and the LDP definition of §3.3 (proof p. 27, (35)–(37))

import Mathlib
import Definitions.Def_HeavyTailNV_Tail_Model
import Definitions.Def_SelfStructIS_LogEff_Setting
import Definitions.Def_SelfStructIS_LogEff_Sampler
import Definitions.Def_SelfStructIS_LogEff_Tail

open MeasureTheory Filter Topology

namespace SelfStructIS.LogEff

theorem theorem_3_1 (d : ℕ) (hd : 0 < d) (ν : Measure (Fin d → ℝ)) [IsProbabilityMeasure ν]
    (p φ I : (Fin d → ℝ) → ℝ)
    (hdens : ν = volume.withDensity (fun y => ENNReal.ofReal (p y * Real.exp (-φ y))))
    (hsupp : ν {y | ∀ i, 0 ≤ y i}ᶜ = 0)
    (hI : ∀ y : Fin d → ℝ, (∀ i, 0 ≤ y i) → 0 ≤ I y)
    (h13 : Conv13 p φ I) :
    IsLDP (fun t : ℝ => ν.map (fun y => t⁻¹ • y)) (rateExt I) := by sorry

end SelfStructIS.LogEff
