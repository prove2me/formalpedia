-- Prove2me | Theorems.Thm_QVolTransducer_Supplement_theorem_9_13
-- name    : QVolTransducer.Supplement.theorem_9_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:45:33.432195+00:00
-- url     : https://prove2.me/theorems/51c189bd-c72a-4f16-b48c-d3a4039432fc
-- title:
--   Theorem 9.13 — annealing $|\pi_{\beta,\delta,r,\zeta}\rangle\rightsquigarrow|\pi_{\beta',\delta',r',\zeta}\rangle$ with complexity $O(\sqrt{d/(\beta'\delta^2)+(\delta'/\delta)^d})$
-- statement:
--   Let $d\in\mathbb N$, $R\ge1$, $0\le\beta'\le\beta$ with $\beta-\beta'\le\max\{\frac1{8\sqrt d},\frac1{8R\sqrt\beta}\}\beta$, $\xi=\sqrt{1+3\ln(20)/(2d)}$, $r\ge\max\{1,\sqrt{d/\beta}\,\xi\}$, $r'\ge\max\{r,\sqrt{d/\beta'}\,\xi\}$,
--
--   $$0<\delta\le\min\Big\{\frac1{4\beta r},\frac1{2^{18}\sqrt{2d\beta}},\frac1{2^{18}\sqrt d}\Big\},\qquad \delta\le\delta'\le\min\Big\{\frac1{4\beta'r'},\frac1{2^{18}\sqrt{2d\beta'}},\frac1{2^{18}\sqrt d}\Big\}.$$
--
--   For a convex body $B_d\subseteq K\subseteq RB_d$ accessible through a membership oracle on a grid with sufficiently small spacing $\zeta=\zeta(d,R,\beta,\beta',\delta,\delta')>0$, there is a bidirectional canonical transducer $A$ with
--
--   $$|\pi_{\beta,\delta,r,\zeta}\rangle\overset{A}{\rightsquigarrow}|\pi_{\beta',\delta',r',\zeta}\rangle,\qquad\text{complexity}\le c\sqrt{\frac{d}{\beta'\delta^2}+\Big(\frac{\delta'}\delta\Big)^d}$$
--
--   for a universal constant $c>0$, where $\pi_{\beta,\delta,r,\zeta}$ is the stationary distribution of the discretized speedy walk on $(K\cap rB_d)_\zeta$.
--
--   This bound is incomparable with that of Theorem 9.14, which trades the $(\delta'/\delta)^d$ term for a factor $1+d\ln(\delta'/\delta)$.
--
--   **Formalization Note** Hypotheses, quantifier order and encodings are those of the published Theorem 9.14: states zero-extended to $\mathbb C^{(RB_d)_\zeta}$ with a possible further $K$-independent summand of the public space, $r\ge\sqrt{d/\beta}\,\xi$ as $d\xi^2\le\beta r^2$, multiplicative δ-constraints, one transducer chosen before $K$.
--
--   Differences from the source:
--   - reading: O(·) → a universal constant c > 0 chosen before every parameter, input and transducer; reason: §2.1's O-notation with the quantification of the published base theorems (base decisions 3–4)
--   - reading: a sufficiently small choice of ζ = ζ(d, R, β, β′, δ, δ′) → ∃ ζ₀ > 0 depending only on d, R, β, β′, δ, δ′, ∀ ζ ∈ (0, ζ₀], uniformly over K; reason: base decision 5
--   - encoding: r ≥ max{1, √(d/β)ξ}, r′ ≥ max{r, √(d/β′)ξ} with ξ = √(1 + 3 ln(20)/(2d)) → 1 ≤ r, d(1 + 3 ln 20/(2d)) ≤ βr², r ≤ r′, d(1 + 3 ln 20/(2d)) ≤ β′r′²; reason: equivalent for β, β′ > 0; at β′ = 0 no real r′ qualifies, in the paper and in Lean (as in the published Theorem 9.14)
--   - encoding: the δ-ranges with 1/(4βr), 1/(2¹⁸√(2dβ)), 1/(2¹⁸√d) (and primed) → 4βrδ ≤ 1, 2¹⁸√(2dβ)δ ≤ 1, 2¹⁸√d δ ≤ 1 (and primed); reason: equivalent for β > 0, and keeps β = 0 where the printed bounds are +∞
--   - encoding: |π_{β,δ,r,ζ}⟩ ∈ ℂ^{(K∩rB_d)_ζ} → the published gridState (speedyStat (K ∩ rB_d) β δ ζ R) in ℂ^{(RB_d)_ζ}, embedded in a public space with a K-independent summand; reason: the zero extension of p.53
--   - encoding: convex body B_d ⊆ K ⊆ RB_d → IsCompact K, Convex ℝ K, closedBall 0 1 ⊆ K ⊆ closedBall 0 R in EuclideanSpace ℝ (Fin d); reason: a convex body is a compact convex set; d ∈ ℕ = {1, 2, …} gives 1 ≤ d
-- source:
--   Cornelissen, Apers, Gribling, Improved quantum volume estimation with transducers and amortized quantum walks, arXiv:2609.40217 (version of November 3, 2026, sha256 40d7b52d…), Theorem 9.13, p.59 (PDF p.61)

import Mathlib
import Definitions.Def_QVolTransducer_BiCanonical
import Definitions.Def_QVolTransducer_speedyStat

namespace QVolTransducer.Supplement

/-- **One annealing step between clipped speedy-walk states** (Cornelissen, Apers, Gribling,
*Improved quantum volume estimation with transducers and amortized quantum walks*, arXiv:2609.40217
(version of November 3, 2026, sha256 40d7b52d…), Theorem 9.13, p.59 (PDF p.61)).

There is a universal constant `c > 0` such that for all `d ≥ 1`, `R ≥ 1`, `β, β', δ, δ'` there is
`ζ₀ = ζ₀(d, R, β, β', δ, δ') > 0` with the following property. Let `0 ≤ β' ≤ β` with
`β − β' ≤ max{1/(8√d), 1/(8R√β)} β`, let `ξ = √(1 + 3 ln(20)/(2d))`, `r ≥ max{1, √(d/β) ξ}`,
`r' ≥ max{r, √(d/β') ξ}`, `0 < δ ≤ min{1/(4βr), 1/(2¹⁸√(2dβ)), 1/(2¹⁸√d)}` and
`δ ≤ δ' ≤ min{1/(4β'r'), 1/(2¹⁸√(2dβ')), 1/(2¹⁸√d)}`. Then for every `0 < ζ ≤ ζ₀` there is one
bidirectional canonical transducer `A`, querying `O_{K,ζ}` on `(RB_d)_ζ`, such that for every
convex body `B_d ⊆ K ⊆ RB_d`: `|π_{β,δ,r,ζ}⟩ ⇝_A |π_{β',δ',r',ζ}⟩` with complexity at most
`c √(d/(β'δ²) + (δ'/δ)^d)`, where `π_{β,δ,r,ζ}` is the stationary distribution of the discretized
speedy walk on `(K ∩ rB_d)_ζ` (the published `speedyStat` of `K ∩ rB_d`).

**Formalization Note** The hypotheses, quantifier order and encodings are those of the published
`QVolTransducer.theorem_9_14` (same paper, p.60): states are zero-extended to `ℂ^{(RB_d)_ζ}` (p.53)
and the public space may carry a further `K`-independent summand; `r ≥ √(d/β) ξ` is written
`dξ² ≤ βr²` and `r' ≥ √(d/β') ξ` as `dξ² ≤ β'r'²` (so `β' > 0`, as no real `r'` exists at
`β' = 0`); the δ-constraints are written multiplicatively. "Sufficiently small `ζ`" is
`∃ ζ₀ > 0, ∀ ζ ∈ (0, ζ₀]` with `ζ₀` depending only on `d, R, β, β', δ, δ'`, and one transducer is
chosen before `K`. `O(·)` is a universal constant `c`. -/
theorem theorem_9_13 :
    ∃ c : ℝ, 0 < c ∧ ∀ (d : ℕ) (R β β' δ δ' : ℝ), ∃ ζ₀ : ℝ, 0 < ζ₀ ∧ ∀ r r' : ℝ,
      1 ≤ d → 1 ≤ R → 0 ≤ β' → β' ≤ β →
      β - β' ≤ max (1 / (8 * Real.sqrt d)) (1 / (8 * R * Real.sqrt β)) * β →
      1 ≤ r → (d : ℝ) * (1 + 3 * Real.log 20 / (2 * d)) ≤ β * r ^ 2 →
      r ≤ r' → (d : ℝ) * (1 + 3 * Real.log 20 / (2 * d)) ≤ β' * r' ^ 2 →
      0 < δ → 4 * β * r * δ ≤ 1 → 2 ^ 18 * Real.sqrt (2 * d * β) * δ ≤ 1 →
      2 ^ 18 * Real.sqrt d * δ ≤ 1 →
      δ ≤ δ' → 4 * β' * r' * δ' ≤ 1 → 2 ^ 18 * Real.sqrt (2 * d * β') * δ' ≤ 1 →
      2 ^ 18 * Real.sqrt d * δ' ≤ 1 →
      ∀ ζ : ℝ, 0 < ζ → ζ ≤ ζ₀ →
        ∃ (e n : ℕ) (A : BiCanonical (Grid d ζ R ⊕ Fin e) (Grid d ζ R) (Fin n)),
          ∀ K : Set (EuclideanSpace ℝ (Fin d)), IsCompact K → Convex ℝ K →
            Metric.closedBall 0 1 ⊆ K → K ⊆ Metric.closedBall 0 R →
            TransducesWithin (A.apply (gridOracle K ζ R))
              (embL (gridState (speedyStat (K ∩ Metric.closedBall 0 r) β δ ζ R)))
              (embL (gridState (speedyStat (K ∩ Metric.closedBall 0 r') β' δ' ζ R)))
              (c * Real.sqrt (d / (β' * δ ^ 2) + (δ' / δ) ^ d)) := by sorry

end QVolTransducer.Supplement
