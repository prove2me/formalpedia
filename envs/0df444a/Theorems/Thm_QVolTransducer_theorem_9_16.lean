-- Prove2me | Theorems.Thm_QVolTransducer_theorem_9_16
-- name    : QVolTransducer.theorem_9_16
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:27:03.463916+00:00
-- url     : https://prove2.me/theorems/a75098f5-8770-4f55-b440-09d2be8da2f6
-- title:
--   Theorem 9.16 — rejection sampling $|\pi_{\beta,\delta,r,\zeta}\rangle\rightsquigarrow|\tilde\pi_{\beta,r,\zeta/\gamma}\rangle$ and reflection through it
-- statement:
--   There is a universal constant $c>0$ such that for all $d,R,\beta,\delta$ there is $\zeta_0=\zeta_0(d,R,\beta,\delta)>0$ with the following property. Let $d\ge1$, $R\ge1$, $\beta\ge0$, $r\ge1$, $\eta>0$,
--
--   $$
--   0<\delta\le\min\Bigl\{\frac1{4\beta r},\frac1{4096\sqrt{2d\beta}},\frac1{4096\sqrt{d\ln(20d/\eta)}}\Bigr\},
--   $$
--
--   $\gamma=1-\frac1{2d}$ and $0<\zeta\le\zeta_0$. For a convex body $B_d\subseteq K\subseteq RB_d$ let $a$, $A_\zeta$ and $\tilde\pi_{\beta,r,\zeta/\gamma}(x)=\pi_{\beta,\delta,r,\zeta}(\gamma x)a(\gamma x)/A_\zeta$ be as in the theorem, and let $\pi_{\beta,r,\zeta/\gamma}$ be the discretization of $\pi_{\beta,r}$ on $(K\cap rB_d)_{\zeta/\gamma}$. Then:
--
--   1. $\|\tilde\pi_{\beta,r,\zeta/\gamma}-\pi_{\beta,r,\zeta/\gamma}\|_{\mathrm{TV}}\le\eta$ for every such $K$;
--   2. there is one bidirectional canonical transducer $C$, querying $O_{K,\zeta}$ and $O_{K,\zeta/\gamma}$, with $|\pi_{\beta,\delta,r,\zeta}\rangle\overset{C}{\rightsquigarrow}|\tilde\pi_{\beta,r,\zeta/\gamma}\rangle$ with complexity at most $c\sqrt{d/(\beta\delta^2)}$, for every such $K$;
--   3. there is one bidirectional canonical transducer $V$, querying $O_{K,\zeta}$ and $O_{K,\zeta/\gamma}$, such that for every such $K$: $|\tilde\pi_{\beta,r,\zeta/\gamma}\rangle\overset{V}{\rightsquigarrow}|\tilde\pi_{\beta,r,\zeta/\gamma}\rangle$ with complexity at most $c$, and $|\bar\psi\rangle\overset{V}{\rightsquigarrow}-|\bar\psi\rangle$ with complexity at most
--
--   $$
--   c\Bigl(\frac{d\,\||\bar\psi\rangle\|^2}{\beta\delta^2}+\sum_{x\in(\gamma(K\cap rB_d))_\zeta}\frac{|\bar\psi(x/\gamma)|^2}{\pi_{\beta,\delta,r,\zeta}(x)\,\ell_{\delta,r,\zeta}(x)}\Bigr)
--   $$
--
--   for every $|\bar\psi\rangle\in\mathbb C^{(K\cap rB_d)_{\zeta/\gamma}}$ orthogonal to $|\tilde\pi_{\beta,r,\zeta/\gamma}\rangle$, where $\bar\psi(x):=\sqrt{\tilde\pi_{\beta,r,\zeta/\gamma}(x)}\,\langle x|\bar\psi\rangle$.
--
--   This converts the speedy-walk state into an approximate Gibbs state on which the mean and quantile estimators run.
--
--   Differences from the source:
--   - encoding: δ ≤ min{1/(4βr), 1/(4096√(2dβ)), …} → 4βrδ ≤ 1, 4096√(2dβ)δ ≤ 1, …; reason: at β = 0 the paper's 1/(4βr) is +∞; the multiplicative form keeps β = 0 in the domain, whereas Lean's 1/0 = 0 would force δ ≤ 0
--   - encoding: complexity bounds with β in a denominator (= +∞ at β = 0) → the bounds multiplied by √β·δ (for C) and βδ² (for the reflection of |ψ̄⟩), so at β = 0 only the actions are asserted; reason: Lean's division by zero returns 0
--   - encoding: δ ≤ 1/(4096√(d ln(20d/η))) for any η > 0 → η < 20d and 4096√(d ln(20d/η))δ ≤ 1; reason: for η ≥ 20d the logarithm is ≤ 0 and the paper's bound is undefined; the added condition excludes only those cases
--   - encoding: x ∈ (K ∩ rB_d)_{ζ/γ} and γx ∈ ζℤ^d → both indexed by the same z ∈ ℤ^d (x = (ζ/γ)z, γx = ζz); reason: the grids ζ/γ·ℤ^d and ζℤ^d are scaled copies
--   - reading: for sufficiently small ζ = ζ(listed parameters) > 0 we can construct a (canonical) transducer → ∃ ζ₀ > 0 depending only on the listed parameters, ∀ ζ ∈ (0, ζ₀], ∃ one transducer, ∀ admissible K; reason: paper.md decision 5; a canonical transducer does not depend on the input (Definition 2.10)
--   - encoding: O(·) complexity → ∃ universal c > 0 fixed before every parameter, K and ζ, with W ≤ c·(bound); reason: paper.md decision 4
--   - reading: C maps a state of ℂ^{(K∩rB_d)_ζ} to one of ℂ^{(K∩rB_d)_{ζ/γ}}; V acts on ℂ^{(K∩rB_d)_{ζ/γ}} → zero extensions to ℂ^{(RB_d)_ζ} ⊕ ℂ^{(RB_d)_{ζ/γ}} (for C, the canonical V_I ⊕ V_O of p.14) and ℂ^{(RB_d)_{ζ/γ}} (for V), each possibly with a further K-independent summand; reason: Definition 2.10 forbids input-dependent public spaces; p.53 extends distributions by zero (paper.md decision 6)
-- source:
--   Cornelissen, Apers, Gribling, Improved quantum volume estimation with transducers and amortized quantum walks, arXiv:2609.40217 (version of November 3, 2026, sha256 40d7b52d…), Theorem 9.16, p.61 (PDF p.63)

import Mathlib
import Definitions.Def_QVolTransducer_BiCanonical
import Definitions.Def_QVolTransducer_rejStat

namespace QVolTransducer

open Classical in
/-- **Rejection sampling from the speedy walk to the Gibbs distribution** (Cornelissen, Apers,
Gribling, *Improved quantum volume estimation with transducers and amortized quantum walks*,
arXiv:2609.40217 (version of November 3, 2026, sha256 40d7b52d…), Theorem 9.16, p.61 (PDF p.63)).

There is a universal constant `c > 0` such that for all `d ≥ 1`, `R ≥ 1`, `β ≥ 0` and `δ` there is
`ζ₀ = ζ₀(d, R, β, δ) > 0` with the following property. Let `r ≥ 1`, `η > 0`,
`0 < δ ≤ min{1/(4βr), 1/(4096√(2dβ)), 1/(4096√(d ln(20d/η)))}`, `γ = 1 − 1/(2d)` and
`0 < ζ ≤ ζ₀`. For a convex body `B_d ⊆ K ⊆ RB_d` let `a`, `A_ζ`, `π̃_{β,r,ζ/γ}` and
`π_{β,r,ζ/γ}` be as in the theorem (`π̃_{β,r,ζ/γ}(x) = π_{β,δ,r,ζ}(γx) a(γx)/A_ζ` on
`(K ∩ rB_d)_{ζ/γ}`, and `π_{β,r,ζ/γ}` the discretization of `π_{β,r}`). Then
1. `‖π̃_{β,r,ζ/γ} − π_{β,r,ζ/γ}‖_TV ≤ η` for every such `K`;
2. there is one bidirectional canonical transducer `C`, querying `O_{K,ζ}` and `O_{K,ζ/γ}`, with
   `|π_{β,δ,r,ζ}⟩ ⇝_C |π̃_{β,r,ζ/γ}⟩` with complexity at most `c √(d/(βδ²))` for every such `K`;
3. there is one bidirectional canonical transducer `V`, querying `O_{K,ζ}` and `O_{K,ζ/γ}`, with
   `|π̃_{β,r,ζ/γ}⟩ ⇝_V |π̃_{β,r,ζ/γ}⟩` with complexity at most `c`, and `|ψ̄⟩ ⇝_V −|ψ̄⟩` with
   complexity at most
   `c (d‖|ψ̄⟩‖²/(βδ²) + Σ_{x ∈ (γ(K∩rB_d))_ζ} |ψ̄(x/γ)|²/(π_{β,δ,r,ζ}(x) ℓ_{δ,r,ζ}(x)))` for every
   `|ψ̄⟩ ∈ ℂ^{(K∩rB_d)_{ζ/γ}}` orthogonal to `|π̃_{β,r,ζ/γ}⟩`, where
   `ψ̄(x) := √(π̃_{β,r,ζ/γ}(x)) ⟨x|ψ̄⟩`.

**Formalization Note** A point `x = (ζ/γ) z` of the grid `ζ/γ ℤ^d` and the point `γx = ζ z` of
`ζℤ^d` share the index `z ∈ ℤ^d`. States are zero-extended to `ℂ^{(RB_d)_ζ}` and
`ℂ^{(RB_d)_{ζ/γ}}` (p.53); `C` maps between the two (public space `V_I ⊕ V_O`, p.14). Each public
space may carry a further `K`-independent summand. The δ-constraints are multiplicative, so
`β = 0` is included; the bounds with `β` in a denominator are stated multiplied by `√β δ` or
`βδ²`, so at `β = 0` (bound `+∞`) only the action is asserted. `η < 20d` is assumed so that
`ln(20d/η) > 0` (otherwise `1/(4096√(d ln(20d/η)))` is undefined). `ζ₀` does not depend on `r`,
`η`, as printed. -/
theorem theorem_9_16 :
    ∃ c : ℝ, 0 < c ∧ ∀ (d : ℕ) (R β δ : ℝ), ∃ ζ₀ : ℝ, 0 < ζ₀ ∧ ∀ r η : ℝ,
      1 ≤ d → 1 ≤ R → 0 ≤ β → 1 ≤ r → 0 < η → η < 20 * d → 0 < δ → 4 * β * r * δ ≤ 1 →
      4096 * Real.sqrt (2 * d * β) * δ ≤ 1 →
      4096 * Real.sqrt (d * Real.log (20 * d / η)) * δ ≤ 1 →
      ∀ ζ : ℝ, 0 < ζ → ζ ≤ ζ₀ →
        (∀ K : Set (EuclideanSpace ℝ (Fin d)), IsCompact K → Convex ℝ K →
          Metric.closedBall 0 1 ⊆ K → K ⊆ Metric.closedBall 0 R →
          tvGrid (gridIdx d (ζ / shrink d) R) (rejStat K β δ r ζ R)
            (gibbsGrid (K ∩ Metric.closedBall 0 r) β (ζ / shrink d) R) ≤ η) ∧
        (∃ (e n : ℕ) (C : BiCanonical ((Grid d ζ R ⊕ Grid d (ζ / shrink d) R) ⊕ Fin e)
            (Grid d ζ R ⊕ Grid d (ζ / shrink d) R) (Fin n)),
          ∀ K : Set (EuclideanSpace ℝ (Fin d)), IsCompact K → Convex ℝ K →
            Metric.closedBall 0 1 ⊆ K → K ⊆ Metric.closedBall 0 R →
            ∃ w, TransducesWith (C.apply (twoGridOracle K ζ (ζ / shrink d) R))
                (embL (embL (gridState (speedyStat (K ∩ Metric.closedBall 0 r) β δ ζ R))))
                (embL (embR (gridState (rejStat K β δ r ζ R)))) w ∧
              ‖w‖ ^ 2 * (Real.sqrt β * δ) ≤ c * Real.sqrt d) ∧
        (∃ (e n : ℕ) (V : BiCanonical (Grid d (ζ / shrink d) R ⊕ Fin e)
            (Grid d ζ R ⊕ Grid d (ζ / shrink d) R) (Fin n)),
          ∀ K : Set (EuclideanSpace ℝ (Fin d)), IsCompact K → Convex ℝ K →
            Metric.closedBall 0 1 ⊆ K → K ⊆ Metric.closedBall 0 R →
            TransducesWithin (V.apply (twoGridOracle K ζ (ζ / shrink d) R))
              (embL (gridState (rejStat K β δ r ζ R)))
              (embL (gridState (rejStat K β δ r ζ R))) c ∧
            ∀ ψ : EuclideanSpace ℂ (Grid d (ζ / shrink d) R),
              (∀ z : Grid d (ζ / shrink d) R,
                latticePt (ζ / shrink d) z.1 ∉ K ∩ Metric.closedBall 0 r → ψ z = 0) →
              inner ℂ (gridState (rejStat K β δ r ζ R) :
                EuclideanSpace ℂ (Grid d (ζ / shrink d) R)) ψ = 0 →
              ∃ w, TransducesWith (V.apply (twoGridOracle K ζ (ζ / shrink d) R))
                  (embL ψ) (embL (-ψ)) w ∧
                β * δ ^ 2 * ‖w‖ ^ 2 ≤
                  c * ((d : ℝ) * ‖ψ‖ ^ 2 + β * δ ^ 2 *
                    ∑ z ∈ Finset.univ.filter (fun z : Grid d (ζ / shrink d) R =>
                        latticePt (ζ / shrink d) z.1 ∈ K ∩ Metric.closedBall 0 r),
                      ‖((Real.sqrt (rejStat K β δ r ζ R z.1) : ℝ) : ℂ) * ψ z‖ ^ 2 /
                        (speedyStat (K ∩ Metric.closedBall 0 r) β δ ζ R z.1 *
                          localCondGrid (K ∩ Metric.closedBall 0 r) δ ζ R z.1))) := by sorry

end QVolTransducer
