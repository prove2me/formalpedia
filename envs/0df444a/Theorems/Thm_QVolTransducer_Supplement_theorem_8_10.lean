-- Prove2me | Theorems.Thm_QVolTransducer_Supplement_theorem_8_10
-- name    : QVolTransducer.Supplement.theorem_8_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:44:06.634665+00:00
-- url     : https://prove2.me/theorems/eb19127b-8733-4066-a87f-a26e1f68db94
-- title:
--   Theorem 8.10 — for small $\zeta$ the cube speedy walk has conductance $\Omega(\delta\sqrt{\beta/d})$
-- statement:
--   Let $d\in\mathbb N$, $R\ge1$, $\beta\ge0$, $0<\delta<\min\{1/(4\beta R),1/\sqrt{2\beta}\}$. There is $\zeta_0=\zeta_0(d,R,\beta,\delta)>0$ such that for every $0<\zeta\le\zeta_0$ and every convex body $B_d\subseteq K\subseteq RB_d$ the cube speedy walk $P^C_{\beta,\delta,\zeta}$ (Definition 8.4: from $x\in M_{K,\zeta}$ pick $y\in(x_\zeta+M_{\delta B_d,\zeta})\cap M_{K,\zeta}$ uniformly and accept with probability $\min\{1,f(y)/f(x)\}$) satisfies
--
--   $$\varphi(P^C_{\beta,\delta,\zeta})\ge c\,\delta\sqrt{\beta/d}$$
--
--   for a universal constant $c>0$, with respect to its stationary distribution $\pi^C_{\beta,\delta,\zeta}$ (density proportional to $\ell^C_{\delta,\zeta}(x)f(x)$).
--
--   This is the first step in transferring the speedy walk's conductance to the finite walk implemented by the algorithm.
--
--   **Formalization Note** $M_{K,\zeta}=\{x:x_\zeta\in K\}$ with $x_\zeta=\zeta\,\mathrm{round}(x/\zeta)$.
--
--   Differences from the source:
--   - reading: O(·) → a universal constant c > 0 chosen before every parameter, input and transducer; reason: §2.1's O-notation with the quantification of the published base theorems (base decisions 3–4)
--   - reading: a sufficiently small choice of ζ = ζ(d, R, β, δ) → ∃ ζ₀ > 0 depending only on d, R, β, δ, ∀ ζ ∈ (0, ζ₀], uniformly over K; reason: base decision 5
--   - encoding: 0 < δ < min{1/(4βR), 1/√(2β)} → 0 < δ, 4βRδ < 1, √(2β)δ < 1; reason: equivalent for β > 0; at β = 0 the printed bounds are +∞ and the multiplicative form keeps that case
--   - encoding: convex body B_d ⊆ K ⊆ RB_d → IsCompact K, Convex ℝ K, closedBall 0 1 ⊆ K ⊆ closedBall 0 R in EuclideanSpace ℝ (Fin d); reason: a convex body is a compact convex set; d ∈ ℕ = {1, 2, …} gives 1 ≤ d
--   - encoding: the stationary distribution π^C_{β,δ,ζ} of the walk → the probability measure with density ∝ ℓ^C_{δ,ζ}(x) e^{−β‖x‖²} on M_{K,ζ} (cubeStat); reason: the density stated on p.48 (via Theorem 7.7)
-- source:
--   Cornelissen, Apers, Gribling, Improved quantum volume estimation with transducers and amortized quantum walks, arXiv:2609.40217 (version of November 3, 2026, sha256 40d7b52d…), Theorem 8.10, p.50 (PDF p.52)

import Mathlib
import Definitions.Def_QVolTransducer_Supplement_measCond
import Definitions.Def_QVolTransducer_Supplement_metroKernel

namespace QVolTransducer.Supplement

open MeasureTheory
open scoped ENNReal

/-- **Conductance of the cube speedy walk** (Cornelissen, Apers, Gribling, *Improved quantum
volume estimation with transducers and amortized quantum walks*, arXiv:2609.40217 (version of
November 3, 2026, sha256 40d7b52d…), Theorem 8.10, p.50 (PDF p.52)).

There is a universal constant `c > 0` such that for all `d ∈ ℕ`, `R ≥ 1`, `β ≥ 0` and
`0 < δ < min{1/(4βR), 1/√(2β)}` there is `ζ₀ = ζ₀(d, R, β, δ) > 0` with the following property:
for every `0 < ζ ≤ ζ₀` and every convex body `B_d ⊆ K ⊆ RB_d`, the cube speedy walk `P^C_{β,δ,ζ}`
(Definition 8.4) has conductance `φ(P^C_{β,δ,ζ}) ≥ c δ √(β/d)`.

**Formalization Note** "For a sufficiently small choice of `ζ = ζ(d, R, β, δ)`" is
`∃ ζ₀ > 0, ∀ ζ ∈ (0, ζ₀]`, with `ζ₀` depending only on `d, R, β, δ` (not on `K`); `Ω(·)` is a
universal constant `c`. The constraints on `δ` are written multiplicatively and strictly
(`4βRδ < 1`, `√(2β) δ < 1`), so `β = 0` is included. The walk lives on `M_{K,ζ} = {x : x_ζ ∈ K}`;
the conductance is that of Definition 6.6 with respect to its stationary distribution `π^C_{β,δ,ζ}`
(density `∝ ℓ^C_{δ,ζ}(x) f(x)` on `M_{K,ζ}`, p.48). -/
theorem theorem_8_10 :
    ∃ c : ℝ, 0 < c ∧
      ∀ (d : ℕ) (R β δ : ℝ), ∃ ζ₀ : ℝ, 0 < ζ₀ ∧
        (1 ≤ d → 1 ≤ R → 0 ≤ β → 0 < δ → 4 * β * R * δ < 1 → Real.sqrt (2 * β) * δ < 1 →
          ∀ ζ : ℝ, 0 < ζ → ζ ≤ ζ₀ →
          ∀ K : Set (EuclideanSpace ℝ (Fin d)), IsCompact K → Convex ℝ K →
            Metric.closedBall 0 1 ⊆ K → K ⊆ Metric.closedBall 0 R →
            ENNReal.ofReal (c * δ * Real.sqrt (β / d)) ≤
              measCond (cubeKernel K β δ ζ) (cubeStat K β δ ζ)) := by sorry

end QVolTransducer.Supplement
