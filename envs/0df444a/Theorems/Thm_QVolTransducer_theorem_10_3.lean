-- Prove2me | Theorems.Thm_QVolTransducer_theorem_10_3
-- name    : QVolTransducer.theorem_10_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:26:59.315399+00:00
-- url     : https://prove2.me/theorems/19b8baa4-9562-40cb-ba63-ca2bf9709295
-- title:
--   Theorem 10.3 — non-destructive quantile estimation over $|\tilde\pi_{\beta,r,\zeta/\gamma}\rangle$
-- statement:
--   There are universal constants $c>0$ and $k\in\mathbb N$ with the following property. Let $d\ge1$, $R\ge1$, $\beta\ge0$, $L>0$, $0<\Delta\le M$, $0<\rho<1$ and an $h$; then there is $\zeta_0=\zeta_0(d,R,\beta,\delta,L,h,\Delta,M,\rho)>0$ such that the following holds for every $r\ge1$, every step size
--
--   $$
--   0<\delta\le\min\Bigl\{\frac1{4\beta r},\frac1{4096\sqrt{2d\beta}},\frac1{4096\sqrt{d\ln(5120d)}}\Bigr\},
--   $$
--
--   every spacing $0<\zeta\le\zeta_0$, $\gamma=1-\frac1{2d}$, and every $X:RB_d\to[0,M]$ that is piecewise $L$-Lipschitz and such that for every $t\in[0,M]$ the partition $RB_d=\{X\le t\}\sqcup\{X>t\}$ is $h$-smooth. There is one bidirectional canonical transducer, querying $O_{K,\zeta}$ and $O_{K,\zeta/\gamma}$, whose read-out values $\tilde m$ lie in $[0,M]$, such that for every convex body $B_d\subseteq K\subseteq RB_d$ with
--
--   $$
--   Q_X(9/16)-Q_X(7/16)\ge\Delta,\qquad Q_X(p):=\inf\{t\in[0,M]:\mathbb P_{x\sim\pi_{\beta,r}}[X(x)\le t]\ge p\},
--   $$
--
--   the transducer, run on $|\tilde\pi_{\beta,r,\zeta/\gamma}\rangle$, restores it and outputs $\tilde m$ with transduction complexity at most
--
--   $$
--   c\,(1+\log(M/\Delta))\,\log(2+1/\rho)\,\sqrt{\frac d{\beta\delta^2}}\,\bigl(\log(2+M/\Delta)\log(2+1/\rho)\bigr)^k ,
--   $$
--
--   and with probability at least $1-\rho$ we have $Q_X(1/8)\le\tilde m\le Q_X(7/8)$, and consequently $|\tilde m-\mu|\le\sqrt7\,\sigma$, where $\mu$ and $\sigma^2$ are the mean and variance of $X$ under $\pi_{\beta,r}$.
--
--   The quantile estimate supplies the initial guess $\tilde m$ that the mean estimation of Theorem 10.2 requires.
--
--   Differences from the source:
--   - reading: Õ((1 + log(M/Δ)) log(1/ρ) √(d/(βδ²))) → ∃ universal c > 0, k ∈ ℕ with W ≤ c·(1 + log(M/Δ))·log(2 + 1/ρ)·√(d/(βδ²))·(log(2 + M/Δ)·log(2 + 1/ρ))^k; reason: the tilde hides polylogarithmic factors in M/Δ and 1/ρ; log(1/ρ) → 0 as ρ → 1 although one estimate has positive cost (paper.md decision 4)
--   - encoding: complexity bound √(d/(βδ²)) (= +∞ at β = 0) → the bound multiplied by √β·δ, so at β = 0 only the action and the output guarantee are asserted; reason: Lean's division by zero returns 0
--   - encoding: δ ≤ min{1/(4βr), 1/(4096√(2dβ)), …} → 4βrδ ≤ 1, 4096√(2dβ)δ ≤ 1, …; reason: at β = 0 the paper's 1/(4βr) is +∞; the multiplicative form keeps β = 0 in the domain, whereas Lean's 1/0 = 0 would force δ ≤ 0
--   - reading: for sufficiently small ζ = ζ(listed parameters) > 0 we can construct a (canonical) transducer → ∃ ζ₀ > 0 depending only on the listed parameters, ∀ ζ ∈ (0, ζ₀], ∃ one transducer, ∀ admissible K; reason: paper.md decision 5; a canonical transducer does not depend on the input (Definition 2.10)
--   - reading: a transducer that when run on |π̃⟩ restores it and outputs a value m̃ ∈ [0, M], with probability ≥ 1 − ρ in [Q_X(1/8), Q_X(7/8)] → |π̃⟩ ⊗ |0⟩ ⇝ |π̃⟩ ⊗ φ_K on an output register (answer and garbage); m̃ = val(i) for the measured answer i, val fixed before K with values in [0, M]; the probability is Σ |φ_K(i,j)|² over the event; reason: outputs of a canonical transducer are measured registers of a K-independent public space (paper.md decision 6)
--   - reading: states on K_ζ (public space ℂ^{K_ζ}) → states zero-extended to ℂ^{(RB_d)_ζ}; the public space may carry a further K-independent summand ℂ^e on which the stated states vanish; reason: Definition 2.10 forbids input-dependent public spaces; p.53 extends distributions by zero; the proof of Theorem 9.2 works on K_ζ ⊔ E (paper.md decision 6)
--   - reading: "a bidirectional canonical a transducer" → a bidirectional canonical transducer; reason: typo (paper.md decision 10)
--   - reading: X a piecewise L-Lipschitz continuous random variable (partition and its smoothness function unnamed) → X is L-Lipschitz on each piece of some h′-smooth Jordan-measurable partition of RB_d, with n, the pieces and h′ existential; the named h is the smoothness function of the sublevel partitions {X ≤ t} ⊔ {X > t}; reason: the theorem names h only for the sublevel partitions, and ζ = ζ(d, R, β, δ, L, h, Δ, M, ρ) depends on that h (the proof applies Lemma 7.5 to 1_{X(x) ≤ t})
--   - reading: "with probability at least 1 − ρ, Q_X(1/8) ≤ m̃ ≤ Q_X(7/8). Consequently, |m̃ − µ| ≤ √7σ" → one event of probability ≥ 1 − ρ containing both Q_X(1/8) ≤ m̃ ≤ Q_X(7/8) and |m̃ − µ| ≤ √7σ; reason: "consequently" derives the second bound from the first on the same outcome (quantile inequality, proof p.70)
-- source:
--   Cornelissen, Apers, Gribling, Improved quantum volume estimation with transducers and amortized quantum walks, arXiv:2609.40217 (version of November 3, 2026, sha256 40d7b52d…), Theorem 10.3, p.69 (PDF p.71)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Query
import Definitions.Def_QVolTransducer_BiCanonical
import Definitions.Def_QVolTransducer_rejStat
import Definitions.Def_QVolTransducer_partitionFn
import Definitions.Def_QVolTransducer_IsPiecewiseLipschitz
import Definitions.Def_QVolTransducer_readMean

namespace QVolTransducer

open QAlgorithms

/-- **Non-destructive quantile estimation over the rejection-sampled Gibbs state** (Cornelissen,
Apers, Gribling, *Improved quantum volume estimation with transducers and amortized quantum walks*,
arXiv:2609.40217 (version of November 3, 2026, sha256 40d7b52d…), Theorem 10.3, p.69 (PDF p.71)).

There are universal constants `c > 0` and `k ∈ ℕ` such that for all `d ≥ 1`, `R ≥ 1`, `β ≥ 0`,
`δ`, `L > 0`, `h`, `0 < Δ ≤ M` and `0 < ρ < 1` there is
`ζ₀ = ζ₀(d, R, β, δ, L, h, Δ, M, ρ) > 0` with the following property. Let `r ≥ 1`,
`0 < δ ≤ min{1/(4βr), 1/(4096√(2dβ)), 1/(4096√(d ln(5120d)))}`, `0 < ζ ≤ ζ₀`, `γ = 1 − 1/(2d)`,
`Ω = RB_d`, and let `X : Ω → [0, M]` be piecewise `L`-Lipschitz such that for every `t ∈ [0, M]`
the partition `Ω = {X ≤ t} ⊔ {X > t}` is `h`-smooth. Then there is one bidirectional canonical
transducer, querying `O_{K,ζ}` and `O_{K,ζ/γ}`, with an output register whose read-out values
`m̃` lie in `[0, M]`, such that for every convex body `B_d ⊆ K ⊆ RB_d` with
`Q_X(9/16) − Q_X(7/16) ≥ Δ`, where `Q_X(p) := inf{t ∈ [0, M] : P_{x∼π_{β,r}}[X(x) ≤ t] ≥ p}`:
run on `|π̃_{β,r,ζ/γ}⟩` it restores it and outputs `m̃`, with complexity at most
`c (1 + log(M/Δ)) log(2 + 1/ρ) √(d/(βδ²)) (log(2+M/Δ) log(2+1/ρ))^k`, and with probability at
least `1 − ρ`, `Q_X(1/8) ≤ m̃ ≤ Q_X(7/8)`, and consequently `|m̃ − µ| ≤ √7 σ`, where `µ` and `σ²`
are the mean and variance of `X` over `π_{β,r}`.

**Formalization Note** "Restores it and outputs a value" is the action
`|π̃⟩ ⊗ |0⟩ ⇝ |π̃⟩ ⊗ φ_K` on an output register `Fin (a+1) × Fin (g+1)` (answer and garbage), with
`m̃ = val(i)` for the measured answer `i` and `val` fixed before `K`. The tilde is read as a universal
`c` and `k` with `log(2+·)` factors, and `log(1/ρ)` as `log(2+1/ρ)`. The bound is stated multiplied
by `√β δ`, so at `β = 0` only the action and the output guarantee are asserted. The public space
may carry a further `K`-independent summand. The piecewise-Lipschitz partition of `X` itself is
existential; `ζ₀` depends only on the printed parameters (not on `r` or `X`). The paper's "a
bidirectional canonical a transducer" is read as "a bidirectional canonical transducer". -/
theorem theorem_10_3 :
    ∃ c : ℝ, 0 < c ∧ ∃ k : ℕ, ∀ (d : ℕ) (R β δ L : ℝ) (h : ℝ → ℝ) (Δ M ρ : ℝ),
      ∃ ζ₀ : ℝ, 0 < ζ₀ ∧ ∀ r : ℝ,
      1 ≤ d → 1 ≤ R → 0 ≤ β → 1 ≤ r → 0 < ρ → ρ < 1 → 0 < δ →
      4 * β * r * δ ≤ 1 → 4096 * Real.sqrt (2 * d * β) * δ ≤ 1 →
      4096 * Real.sqrt (d * Real.log (5120 * d)) * δ ≤ 1 →
      0 < Δ → Δ ≤ M → 0 < L →
      ∀ ζ : ℝ, 0 < ζ → ζ ≤ ζ₀ →
      ∀ X : EuclideanSpace ℝ (Fin d) → ℝ,
        (∀ x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) R, X x ∈ Set.Icc 0 M) →
        (∃ (n : ℕ) (parts : Fin n → Set (EuclideanSpace ℝ (Fin d))) (h' : ℝ → ℝ),
          IsPiecewiseLipschitz X (Metric.closedBall 0 R) L parts h') →
        (∀ t ∈ Set.Icc 0 M, IsSmoothPartition (Metric.closedBall 0 R)
          ![{x | x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) R ∧ X x ≤ t},
            {x | x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) R ∧ t < X x}] h) →
        ∃ (a g e n : ℕ)
          (V : BiCanonical ((Grid d (ζ / shrink d) R × (Fin (a + 1) × Fin (g + 1))) ⊕ Fin e)
            (Grid d ζ R ⊕ Grid d (ζ / shrink d) R) (Fin n))
          (val : Fin (a + 1) → ℝ),
          (∀ i, val i ∈ Set.Icc 0 M) ∧
          ∀ K : Set (EuclideanSpace ℝ (Fin d)), IsCompact K → Convex ℝ K →
            Metric.closedBall 0 1 ⊆ K → K ⊆ Metric.closedBall 0 R →
            Δ ≤ gibbsQuantile (K ∩ Metric.closedBall 0 r) β X M (9 / 16) -
              gibbsQuantile (K ∩ Metric.closedBall 0 r) β X M (7 / 16) →
            ∃ (φ : EuclideanSpace ℂ (Fin (a + 1) × Fin (g + 1))) (w : EuclideanSpace ℂ _),
              TransducesWith (V.apply (twoGridOracle K ζ (ζ / shrink d) R))
                (embL (tensorVec (gridState (rejStat K β δ r ζ R)) (ket (0, 0))))
                (embL (tensorVec (gridState (rejStat K β δ r ζ R)) φ)) w ∧
              ‖w‖ ^ 2 * (Real.sqrt β * δ) ≤
                c * (1 + Real.log (M / Δ)) * Real.log (2 + 1 / ρ) * Real.sqrt d *
                  (Real.log (2 + M / Δ) * Real.log (2 + 1 / ρ)) ^ k ∧
              1 - ρ ≤ readProb φ val (fun m =>
                gibbsQuantile (K ∩ Metric.closedBall 0 r) β X M (1 / 8) ≤ m ∧
                m ≤ gibbsQuantile (K ∩ Metric.closedBall 0 r) β X M (7 / 8) ∧
                |m - gibbsMean (K ∩ Metric.closedBall 0 r) β X| ≤
                  Real.sqrt 7 * Real.sqrt (gibbsVar (K ∩ Metric.closedBall 0 r) β X)) := by sorry

end QVolTransducer
