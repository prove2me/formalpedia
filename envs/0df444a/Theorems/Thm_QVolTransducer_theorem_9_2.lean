-- Prove2me | Theorems.Thm_QVolTransducer_theorem_9_2
-- name    : QVolTransducer.theorem_9_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:26:11.43574+00:00
-- url     : https://prove2.me/theorems/1d9b4cc8-249a-4dd5-bc61-94ae913678c8
-- title:
--   Theorem 9.2 — amortized reflection through the discretized speedy-walk state $|\pi_{\beta,\delta,\zeta}\rangle$
-- statement:
--   There is a universal constant $c>0$ such that for all $d\ge1$, $R\ge1$, $\beta\ge0$ and step sizes
--
--   $$
--   0<\delta\le\min\Bigl\{\frac1{4\beta R},\frac1{4096\sqrt{2d\beta}},\frac1{4096\sqrt d}\Bigr\}
--   $$
--
--   there is $\zeta_0=\zeta_0(d,R,\beta,\delta)>0$ such that for every spacing $0<\zeta\le\zeta_0$ there is one bidirectional canonical transducer $U$, querying the grid membership oracle $O_{K,\zeta}$, such that for every convex body $B_d\subseteq K\subseteq RB_d$, with $\pi_{\beta,\delta,\zeta}$ the stationary distribution of the discretized speedy walk on $K_\zeta$:
--
--   1. $|\pi_{\beta,\delta,\zeta}\rangle\overset{U}{\rightsquigarrow}|\pi_{\beta,\delta,\zeta}\rangle$ with complexity at most $c$;
--   2. $|\bar\pi\rangle\overset{U}{\rightsquigarrow}-|\bar\pi\rangle$ with complexity at most
--
--   $$
--   c\Bigl(\frac{d\,\||\bar\pi\rangle\|^2}{\beta\delta^2}+\sum_{x\in K_\zeta}\frac{|\bar\pi(x)|^2}{\pi_{\beta,\delta,\zeta}(x)\,\ell_{\delta,\zeta}(x)}\Bigr)
--   $$
--
--   for every $|\bar\pi\rangle\in\mathbb C^{K_\zeta}$ orthogonal to $|\pi_{\beta,\delta,\zeta}\rangle$, where $\bar\pi(x):=\sqrt{\pi_{\beta,\delta,\zeta}(x)}\,\langle x|\bar\pi\rangle$.
--
--   The reflection costs $O(1)$ on the stationary state itself: this is the amortization that makes the volume algorithm's total cost scale with the schedule length rather than with the walk's mixing time per stage.
--
--   Differences from the source:
--   - reading: ⟨π̄|π_{β,δ}⟩ = 0 and the stray "dx" in the sum → orthogonality to |π_{β,δ,ζ}⟩ and no dx; reason: the continuous density π_{β,δ} is not a vector of ℂ^{K_ζ}; typos (paper.md decision 10)
--   - encoding: δ ≤ min{1/(4βR), 1/(4096√(2dβ)), 1/(4096√d)} → 4βRδ ≤ 1, 4096√(2dβ)δ ≤ 1, 4096√dδ ≤ 1; reason: at β = 0 the paper's 1/(4βR) is +∞; Lean's 1/0 = 0 would force δ ≤ 0
--   - encoding: complexity bound d‖|π̄⟩‖²/(βδ²) + Σ … (= +∞ at β = 0) → the bound multiplied by βδ², so at β = 0 only the action is asserted; reason: Lean's division by zero returns 0
--   - reading: for sufficiently small ζ = ζ(listed parameters) > 0 we can construct a (canonical) transducer → ∃ ζ₀ > 0 depending only on the listed parameters, ∀ ζ ∈ (0, ζ₀], ∃ one transducer, ∀ admissible K; reason: paper.md decision 5; a canonical transducer does not depend on the input (Definition 2.10)
--   - encoding: O(·) complexity → ∃ universal c > 0 fixed before every parameter, K and ζ, with W ≤ c·(bound); reason: paper.md decision 4
--   - reading: states on K_ζ (public space ℂ^{K_ζ}) → states zero-extended to ℂ^{(RB_d)_ζ}; the public space may carry a further K-independent summand ℂ^e on which the stated states vanish; reason: Definition 2.10 forbids input-dependent public spaces; p.53 extends distributions by zero; the proof of Theorem 9.2 works on K_ζ ⊔ E (paper.md decision 6)
-- source:
--   Cornelissen, Apers, Gribling, Improved quantum volume estimation with transducers and amortized quantum walks, arXiv:2609.40217 (version of November 3, 2026, sha256 40d7b52d…), Theorem 9.2, p.54 (PDF p.56)

import Mathlib
import Definitions.Def_QVolTransducer_BiCanonical
import Definitions.Def_QVolTransducer_speedyStat

namespace QVolTransducer

open Classical in
/-- **Speedy walk distribution reflection** (Cornelissen, Apers, Gribling, *Improved quantum volume
estimation with transducers and amortized quantum walks*, arXiv:2609.40217 (version of November 3,
2026, sha256 40d7b52d…), Theorem 9.2, p.54 (PDF p.56)).

There is a universal constant `c > 0` such that for all `d ≥ 1`, `R ≥ 1`, `β ≥ 0` and step size
`0 < δ ≤ min{1/(4βR), 1/(4096√(2dβ)), 1/(4096√d)}` there is `ζ₀ = ζ₀(d, R, β, δ) > 0` such that for
every grid spacing `0 < ζ ≤ ζ₀` there is one bidirectional canonical transducer `U`, querying the
membership oracle `O_{K,ζ}` on `(RB_d)_ζ`, such that for every convex body `B_d ⊆ K ⊆ RB_d`, with
`π_{β,δ,ζ}` the stationary distribution of the discretized speedy walk on `K_ζ`:
1. `|π_{β,δ,ζ}⟩ ⇝_U |π_{β,δ,ζ}⟩` with complexity at most `c`;
2. `|π̄⟩ ⇝_U −|π̄⟩` with complexity at most
   `c (d‖|π̄⟩‖²/(βδ²) + Σ_{x∈K_ζ} |π̄(x)|²/(π_{β,δ,ζ}(x) ℓ_{δ,ζ}(x)))` for every `|π̄⟩ ∈ ℂ^{K_ζ}`
   with `⟨π̄|π_{β,δ,ζ}⟩ = 0`, where `π̄(x) := √(π_{β,δ,ζ}(x)) ⟨x|π̄⟩`.

**Formalization Note** States on `K_ζ` live in `ℂ^{(RB_d)_ζ}`, extended by zero (p.53), so the
public space does not depend on `K`; it may carry a further `K`-independent summand `ℂ^e`, on which
the stated states vanish (the paper's proof works on `K_ζ ⊔ E`). The δ-constraints are written
multiplicatively (`4βRδ ≤ 1`, `4096√(2dβ)δ ≤ 1`, `4096√dδ ≤ 1`), so `β = 0` is included with
`1/(4β R) = +∞`; the second bound is stated multiplied by `βδ²`, so at `β = 0` (bound `+∞`) only
the action is asserted. The paper's "`⟨π̄|π_{β,δ}⟩ = 0`" is read as orthogonality to
`|π_{β,δ,ζ}⟩`, and the stray "dx" in its sum is dropped. -/
theorem theorem_9_2 :
    ∃ c : ℝ, 0 < c ∧ ∀ (d : ℕ) (R β δ : ℝ), 1 ≤ d → 1 ≤ R → 0 ≤ β → 0 < δ →
      4 * β * R * δ ≤ 1 → 4096 * Real.sqrt (2 * d * β) * δ ≤ 1 → 4096 * Real.sqrt d * δ ≤ 1 →
      ∃ ζ₀ : ℝ, 0 < ζ₀ ∧ ∀ ζ : ℝ, 0 < ζ → ζ ≤ ζ₀ →
        ∃ (e n : ℕ) (U : BiCanonical (Grid d ζ R ⊕ Fin e) (Grid d ζ R) (Fin n)),
          ∀ K : Set (EuclideanSpace ℝ (Fin d)), IsCompact K → Convex ℝ K →
            Metric.closedBall 0 1 ⊆ K → K ⊆ Metric.closedBall 0 R →
            TransducesWithin (U.apply (gridOracle K ζ R))
              (embL (gridState (speedyStat K β δ ζ R)))
              (embL (gridState (speedyStat K β δ ζ R))) c ∧
            ∀ ψ : EuclideanSpace ℂ (Grid d ζ R),
              (∀ z : Grid d ζ R, latticePt ζ z.1 ∉ K → ψ z = 0) →
              inner ℂ (gridState (speedyStat K β δ ζ R) : EuclideanSpace ℂ (Grid d ζ R)) ψ = 0 →
              ∃ w, TransducesWith (U.apply (gridOracle K ζ R)) (embL ψ) (embL (-ψ)) w ∧
                β * δ ^ 2 * ‖w‖ ^ 2 ≤
                  c * ((d : ℝ) * ‖ψ‖ ^ 2 + β * δ ^ 2 *
                    ∑ z ∈ Finset.univ.filter (fun z : Grid d ζ R => latticePt ζ z.1 ∈ K),
                      ‖((Real.sqrt (speedyStat K β δ ζ R z.1) : ℝ) : ℂ) * ψ z‖ ^ 2 /
                        (speedyStat K β δ ζ R z.1 * localCondGrid K δ ζ R z.1)) := by sorry

end QVolTransducer
