-- Prove2me | Theorems.Thm_QVolTransducer_Supplement_theorem_8_16
-- name    : QVolTransducer.Supplement.theorem_8_16
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:44:43.749097+00:00
-- url     : https://prove2.me/theorems/df354e3f-98b7-463a-9a8c-65d5b2e49f4c
-- title:
--   Theorem 8.16 — conductance approximation: the discretized speedy walk has conductance $\Omega(\delta\sqrt{\beta/d})$
-- statement:
--   Let $d\in\mathbb N$, $\beta\ge0$, $R\ge1$, $0<\delta<\min\{1/(4\beta R),1/\sqrt{2\beta}\}$. There is $\zeta_0=\zeta_0(d,R,\beta,\delta)>0$ such that for every $0<\zeta\le\zeta_0$ and every convex body $B_d\subseteq K\subseteq RB_d$ the discretized speedy walk $P_{\beta,\delta,\zeta}$ on $K_\zeta$ (Definition 8.13: from $x\in K_\zeta$ pick $y\in(K\cap(x+\delta B_d))_\zeta$ uniformly and move with probability $\min\{1,f(y)/f(x)\}$) satisfies
--
--   $$\varphi(P_{\beta,\delta,\zeta})\ge c\,\delta\sqrt{\beta/d}$$
--
--   for a universal constant $c>0$, with respect to its stationary distribution $\pi_{\beta,\delta,\zeta}\propto e^{-\beta\|x\|^2}\ell_{\delta,\zeta}(x)$.
--
--   Through Cheeger's inequality this gives the spectral gap of the walk that the quantum algorithm runs.
--
--   **Formalization Note** $K_\zeta$ is indexed by the grid $(RB_d)_\zeta$ restricted to $K$; the conductance is the finite one of Definition 2.24, and $\pi_{\beta,\delta,\zeta}$ is the published `speedyStat`.
--
--   Differences from the source:
--   - reading: O(·) → a universal constant c > 0 chosen before every parameter, input and transducer; reason: §2.1's O-notation with the quantification of the published base theorems (base decisions 3–4)
--   - reading: a sufficiently small choice of ζ = ζ(d, R, β, δ) → ∃ ζ₀ > 0 depending only on d, R, β, δ, ∀ ζ ∈ (0, ζ₀], uniformly over K; reason: base decision 5
--   - encoding: 0 < δ < min{1/(4βR), 1/√(2β)} → 0 < δ, 4βRδ < 1, √(2β)δ < 1; reason: equivalent for β > 0; at β = 0 the printed bounds are +∞ and the multiplicative form keeps that case
--   - encoding: convex body B_d ⊆ K ⊆ RB_d → IsCompact K, Convex ℝ K, closedBall 0 1 ⊆ K ⊆ closedBall 0 R in EuclideanSpace ℝ (Fin d); reason: a convex body is a compact convex set; d ∈ ℕ = {1, 2, …} gives 1 ≤ d
--   - encoding: the stationary distribution π_{β,δ,ζ} of the walk → the published speedyStat (∝ exp(−β‖x‖²) ℓ_{δ,ζ}(x), p.51); reason: the formula the paper states (base decision 9)
-- source:
--   Cornelissen, Apers, Gribling, Improved quantum volume estimation with transducers and amortized quantum walks, arXiv:2609.40217 (version of November 3, 2026, sha256 40d7b52d…), Theorem 8.16, p.51 (PDF p.53)

import Mathlib
import Definitions.Def_QVolTransducer_speedyStat
import Definitions.Def_QVolTransducer_Supplement_measCond
import Definitions.Def_QVolTransducer_Supplement_metroKernel

namespace QVolTransducer.Supplement

open scoped ENNReal

open Classical in
/-- **Conductance approximation** (Cornelissen, Apers, Gribling, *Improved quantum volume
estimation with transducers and amortized quantum walks*, arXiv:2609.40217 (version of November 3,
2026, sha256 40d7b52d…), Theorem 8.16, p.51 (PDF p.53)).

There is a universal constant `c > 0` such that for all `d ∈ ℕ`, `β ≥ 0`, `R ≥ 1` and
`0 < δ < min{1/(4βR), 1/√(2β)}` there is `ζ₀ = ζ₀(d, R, β, δ) > 0` with the following property:
for every `0 < ζ ≤ ζ₀` and every convex body `B_d ⊆ K ⊆ RB_d`, the discretized speedy walk
`P_{β,δ,ζ}` on `K_ζ` (Definition 8.13) has conductance `φ(P_{β,δ,ζ}) ≥ c δ √(β/d)`.

**Formalization Note** "Sufficiently small `ζ = ζ(d, R, β, δ)`" is `∃ ζ₀ > 0, ∀ ζ ∈ (0, ζ₀]`, with
`ζ₀` independent of `K`; `Ω(·)` is a universal constant. The constraints on `δ` are written
multiplicatively and strictly, so `β = 0` is included. `K_ζ` is indexed by the points of the
published grid `(RB_d)_ζ` lying in `K` (all of `K_ζ` since `K ⊆ RB_d`); the conductance is the
finite one (Definition 2.24) with respect to the stationary distribution, the published
`speedyStat` `π_{β,δ,ζ} ∝ exp(−β‖x‖²) ℓ_{δ,ζ}(x)` (p.51). -/
theorem theorem_8_16 :
    ∃ c : ℝ, 0 < c ∧
      ∀ (d : ℕ) (R β δ : ℝ), ∃ ζ₀ : ℝ, 0 < ζ₀ ∧
        (1 ≤ d → 1 ≤ R → 0 ≤ β → 0 < δ → 4 * β * R * δ < 1 → Real.sqrt (2 * β) * δ < 1 →
          ∀ ζ : ℝ, 0 < ζ → ζ ≤ ζ₀ →
          ∀ K : Set (EuclideanSpace ℝ (Fin d)), IsCompact K → Convex ℝ K →
            Metric.closedBall 0 1 ⊆ K → K ⊆ Metric.closedBall 0 R →
            ENNReal.ofReal (c * δ * Real.sqrt (β / d)) ≤
              finCond (discSpeedyMatrix K β δ ζ R)
                (fun x => speedyStat K β δ ζ R x.1.1)) := by sorry

end QVolTransducer.Supplement
