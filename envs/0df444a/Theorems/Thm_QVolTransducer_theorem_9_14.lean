-- Prove2me | Theorems.Thm_QVolTransducer_theorem_9_14
-- name    : QVolTransducer.theorem_9_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:25:14.931271+00:00
-- url     : https://prove2.me/theorems/63e8093b-d00d-4ac8-b6ed-3b4cd4f66cbe
-- title:
--   Theorem 9.14 — annealing $|\pi_{\beta,\delta,r,\zeta}\rangle\rightsquigarrow|\pi_{\beta',\delta',r',\zeta}\rangle$
-- statement:
--   There is a universal constant $c>0$ such that for all $d,R,\beta,\beta',\delta,\delta'$ there is $\zeta_0=\zeta_0(d,R,\beta,\beta',\delta,\delta')>0$ with the following property. Let $d\ge1$, $R\ge1$, $0\le\beta'\le\beta$ with $\beta-\beta'\le\max\{\frac1{8\sqrt d},\frac1{8R\sqrt\beta}\}\beta$, let $\xi=\sqrt{1+3\ln(20)/(2d)}$, $r\ge\max\{1,\sqrt{d/\beta}\,\xi\}$, $r'\ge\max\{r,\sqrt{d/\beta'}\,\xi\}$,
--
--   $$
--   0<\delta\le\min\Bigl\{\frac1{4\beta r},\frac1{2^{18}\sqrt{2d\beta}},\frac1{2^{18}\sqrt d}\Bigr\},\qquad
--   \delta\le\delta'\le\min\Bigl\{\frac1{4\beta'r'},\frac1{2^{18}\sqrt{2d\beta'}},\frac1{2^{18}\sqrt d}\Bigr\},
--   $$
--
--   and $0<\zeta\le\zeta_0$. Then there is one bidirectional canonical transducer $A$, querying the grid membership oracle $O_{K,\zeta}$, such that for every convex body $B_d\subseteq K\subseteq RB_d$
--
--   $$
--   |\pi_{\beta,\delta,r,\zeta}\rangle\overset{A}{\rightsquigarrow}|\pi_{\beta',\delta',r',\zeta}\rangle
--   \quad\text{with complexity at most}\quad c\sqrt{\frac d{\beta'\delta^2}}\Bigl(1+d\ln\frac{\delta'}\delta\Bigr),
--   $$
--
--   where $\pi_{\beta,\delta,r,\zeta}$ is the stationary distribution of the discretized speedy walk on $(K\cap rB_d)_\zeta$. This is the annealing step between consecutive temperatures of the cooling schedule.
--
--   Differences from the source:
--   - encoding: r ≥ max{1, √(d/β)ξ}, r′ ≥ max{r, √(d/β′)ξ} with ξ = √(1 + 3 ln(20)/(2d)) → 1 ≤ r, d(1 + 3 ln 20/(2d)) ≤ βr², r ≤ r′, d(1 + 3 ln 20/(2d)) ≤ β′r′²; reason: equivalent for β, β′ > 0; at β′ = 0 no real r′ qualifies, in the paper and in Lean
--   - encoding: δ ≤ min{1/(4βr), 1/(2¹⁸√(2dβ)), 1/(2¹⁸√d)} and the same for δ′ → 4βrδ ≤ 1, 2¹⁸√(2dβ)δ ≤ 1, 2¹⁸√dδ ≤ 1 and the same for δ′; reason: avoids Lean's 1/0 = 0; equivalent for positive parameters
--   - reading: for sufficiently small ζ = ζ(listed parameters) > 0 we can construct a (canonical) transducer → ∃ ζ₀ > 0 depending only on the listed parameters, ∀ ζ ∈ (0, ζ₀], ∃ one transducer, ∀ admissible K; reason: paper.md decision 5; a canonical transducer does not depend on the input (Definition 2.10)
--   - encoding: O(·) complexity → ∃ universal c > 0 fixed before every parameter, K and ζ, with W ≤ c·(bound); reason: paper.md decision 4
--   - reading: states on K_ζ (public space ℂ^{K_ζ}) → states zero-extended to ℂ^{(RB_d)_ζ}; the public space may carry a further K-independent summand ℂ^e on which the stated states vanish; reason: Definition 2.10 forbids input-dependent public spaces; p.53 extends distributions by zero; the proof of Theorem 9.2 works on K_ζ ⊔ E (paper.md decision 6)
-- source:
--   Cornelissen, Apers, Gribling, Improved quantum volume estimation with transducers and amortized quantum walks, arXiv:2609.40217 (version of November 3, 2026, sha256 40d7b52d…), Theorem 9.14, p.60 (PDF p.62)

import Mathlib
import Definitions.Def_QVolTransducer_BiCanonical
import Definitions.Def_QVolTransducer_speedyStat

namespace QVolTransducer

/-- **Annealing of speedy walk distributions** (Cornelissen, Apers, Gribling, *Improved quantum
volume estimation with transducers and amortized quantum walks*, arXiv:2609.40217 (version of
November 3, 2026, sha256 40d7b52d…), Theorem 9.14, p.60 (PDF p.62)).

There is a universal constant `c > 0` such that for all `d ≥ 1`, `R ≥ 1`, `β, β', δ, δ'` there is
`ζ₀ = ζ₀(d, R, β, β', δ, δ') > 0` with the following property. Let `0 ≤ β' ≤ β` with
`β − β' ≤ max{1/(8√d), 1/(8R√β)} β`, let `ξ = √(1 + 3 ln(20)/(2d))`, `r ≥ max{1, √(d/β) ξ}`,
`r' ≥ max{r, √(d/β') ξ}`, `0 < δ ≤ min{1/(4βr), 1/(2¹⁸√(2dβ)), 1/(2¹⁸√d)}` and
`δ ≤ δ' ≤ min{1/(4β'r'), 1/(2¹⁸√(2dβ')), 1/(2¹⁸√d)}`. Then for every `0 < ζ ≤ ζ₀` there is one
bidirectional canonical transducer `A`, querying `O_{K,ζ}` on `(RB_d)_ζ`, such that for every
convex body `B_d ⊆ K ⊆ RB_d`:
`|π_{β,δ,r,ζ}⟩ ⇝_A |π_{β',δ',r',ζ}⟩` with complexity at most `c √(d/(β'δ²)) (1 + d ln(δ'/δ))`,
where `π_{β,δ,r,ζ}` is the stationary distribution of the discretized speedy walk on
`(K ∩ rB_d)_ζ`.

**Formalization Note** States are zero-extended to `ℂ^{(RB_d)_ζ}` (p.53) and the public space may
carry a further `K`-independent summand. `r ≥ √(d/β) ξ` is written `dξ² ≤ βr²` and
`r' ≥ √(d/β') ξ` as `dξ² ≤ β'r'²` (so `β' > 0`, as in the paper, where no real `r'` exists at
`β' = 0`); the δ-constraints are written multiplicatively. `ζ₀` does not depend on `r`, `r'`, as
printed. -/
theorem theorem_9_14 :
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
              (c * Real.sqrt (d / (β' * δ ^ 2)) * (1 + d * Real.log (δ' / δ))) := by sorry

end QVolTransducer
