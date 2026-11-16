-- Prove2me | Theorems.Thm_QVolTransducer_Supplement_theorem_8_2
-- name    : QVolTransducer.Supplement.theorem_8_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:43:28.788212+00:00
-- url     : https://prove2.me/theorems/c85533f0-504f-4479-ae79-f2151a18d14f
-- title:
--   Theorem 8.2 — the speedy walk on $B_d\subseteq K\subseteq RB_d$ has conductance $\Omega(\delta\sqrt{\beta/d})$
-- statement:
--   Let $d\in\mathbb N$ and let $B_d\subseteq K\subseteq RB_d$ be a convex body. The speedy walk $P_{\beta,\delta}$ on $K$ (Definition 5.3: from $x$ pick $y\in(x+\delta B_d)\cap K$ uniformly and accept with probability $\min\{1,e^{-\beta\|y\|^2}/e^{-\beta\|x\|^2}\}$), with $\beta\ge0$ and
--
--   $$0<\delta\le\min\Big\{\frac1{4\beta R},\frac1{\sqrt{2\beta}}\Big\},$$
--
--   has conductance
--
--   $$\varphi(P_{\beta,\delta})\ge c\,\delta\sqrt{\beta/d}$$
--
--   for a universal constant $c>0$, with respect to its stationary distribution $\pi_{\beta,\delta}$ (density proportional to $\ell_\delta(x)e^{-\beta\|x\|^2}$ on $K$).
--
--   This slightly generalizes Cousins and Vempala's bound to bodies inside $RB_d$, which the volume algorithm needs for radii $R$ larger than $O(\sqrt{d/\beta})$.
--
--   **Formalization Note** $\Omega(\cdot)$ is a universal constant chosen before $d,R,\beta,\delta,K$. The constraints on $\delta$ are multiplicative, so $\beta=0$ is included (the bound is then $0$).
--
--   Differences from the source:
--   - reading: O(·) → a universal constant c > 0 chosen before every parameter, input and transducer; reason: §2.1's O-notation with the quantification of the published base theorems (base decisions 3–4)
--   - encoding: 0 < δ ≤ min{1/(4βR), 1/√(2β)} → 0 < δ, 4βRδ ≤ 1, √(2β)δ ≤ 1; reason: equivalent for β > 0; at β = 0 the printed bounds are +∞ and the multiplicative form keeps that case
--   - encoding: convex body B_d ⊆ K ⊆ RB_d → IsCompact K, Convex ℝ K, closedBall 0 1 ⊆ K ⊆ closedBall 0 R in EuclideanSpace ℝ (Fin d); reason: a convex body is a compact convex set; d ∈ ℕ = {1, 2, …} gives 1 ≤ d
--   - encoding: the stationary distribution π_{β,δ} of the walk → the probability measure with density ∝ ℓ_δ(x) e^{−β‖x‖²} on K (speedyStatMeas); reason: the density stated on p.38 (via [CV18, Lemma 3.1])
-- source:
--   Cornelissen, Apers, Gribling, Improved quantum volume estimation with transducers and amortized quantum walks, arXiv:2609.40217 (version of November 3, 2026, sha256 40d7b52d…), Theorem 8.2, p.47 (PDF p.49)

import Mathlib
import Definitions.Def_QVolTransducer_Supplement_measCond
import Definitions.Def_QVolTransducer_Supplement_metroKernel

namespace QVolTransducer.Supplement

open MeasureTheory
open scoped ENNReal

/-- **Conductance of the speedy walk** (Cornelissen, Apers, Gribling, *Improved quantum volume
estimation with transducers and amortized quantum walks*, arXiv:2609.40217 (version of November 3,
2026, sha256 40d7b52d…), Theorem 8.2, p.47 (PDF p.49); a slight generalization of [CV18,
Theorem 6.6]).

There is a universal constant `c > 0` with the following property. Let `d ∈ ℕ` and
`B_d ⊆ K ⊆ RB_d` be a convex body. The speedy walk `P_{β,δ}` on `K` (Definition 5.3) with
parameters `β ≥ 0` and `0 < δ ≤ min{1/(4βR), 1/√(2β)}` has conductance at least `c δ √(β/d)`.

**Formalization Note** `Ω(·)` is a universal constant `c` chosen before `d, R, β, δ, K`. A convex
body is a compact convex set; `B_d` is the closed unit ball of `EuclideanSpace ℝ (Fin d)` and
`ℕ = {1, 2, …}`. The constraints on `δ` are written multiplicatively (`4βRδ ≤ 1`, `√(2β) δ ≤ 1`),
so that `β = 0` (where `1/(4βR)` and `1/√(2β)` are `+∞`) is included. The conductance is that of
Definition 6.6 with respect to the stationary distribution `π_{β,δ}` (density `∝ ℓ_δ(x)f(x)` on
`K`, p.38), valued in `[0, ∞]`. -/
theorem theorem_8_2 :
    ∃ c : ℝ, 0 < c ∧
      ∀ (d : ℕ) (R β δ : ℝ) (K : Set (EuclideanSpace ℝ (Fin d))),
        1 ≤ d → IsCompact K → Convex ℝ K → Metric.closedBall 0 1 ⊆ K →
        K ⊆ Metric.closedBall 0 R → 0 ≤ β → 0 < δ → 4 * β * R * δ ≤ 1 →
        Real.sqrt (2 * β) * δ ≤ 1 →
        ENNReal.ofReal (c * δ * Real.sqrt (β / d)) ≤
          measCond (speedyKernel K β δ) (speedyStatMeas K β δ) := by sorry

end QVolTransducer.Supplement
