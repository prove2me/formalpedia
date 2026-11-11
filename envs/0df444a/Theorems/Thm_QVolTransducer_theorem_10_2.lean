-- Prove2me | Theorems.Thm_QVolTransducer_theorem_10_2
-- name    : QVolTransducer.theorem_10_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:26:59.677582+00:00
-- url     : https://prove2.me/theorems/e6bfb629-6e15-42c5-8164-099fc5dea18b
-- title:
--   Theorem 10.2 — non-destructive mean estimation over $|\tilde\pi_{\beta,r,\zeta/\gamma}\rangle$
-- statement:
--   There are universal constants $c>0$ and $k\in\mathbb N$ with the following property. Let $d\ge1$, $R\ge1$, $\beta\ge0$, $0<\epsilon<1$, $M>0$, $L$, $h$ and $\tilde\sigma>0$; then there is $\zeta_0=\zeta_0(d,R,\beta,\delta,\epsilon,M,L,h,\tilde\sigma)>0$ such that the following holds for every $t\ge1$, $r\ge1$, every step size
--
--   $$
--   0<\delta\le\min\Bigl\{\frac1{4\beta r},\frac1{4096\sqrt{2d\beta}},\frac1{4096\sqrt{d\ln(20d/\min\{\epsilon^2/2^{20},\,\epsilon^2/(2^{41}t^2)\})}}\Bigr\},
--   $$
--
--   every spacing $0<\zeta\le\zeta_0$, $\gamma=1-\frac1{2d}$, every $X:RB_d\to[0,M]$ that is piecewise $L$-Lipschitz on an $h$-smooth partition, and every $\tilde m\in\mathbb R$. There is one bidirectional canonical transducer $V$, querying $O_{K,\zeta}$ and $O_{K,\zeta/\gamma}$, with an output register and a readout, such that for every convex body $B_d\subseteq K\subseteq RB_d$ for which the mean $\mu$ and the variance $\sigma^2$ of $X$ under $\pi_{\beta,r}$ satisfy $\sigma\le\tilde\sigma$ and $|\mu-\tilde m|\le17\tilde\sigma$:
--
--   $$
--   |\tilde\pi_{\beta,r,\zeta/\gamma}\rangle\overset{V}{\rightsquigarrow}|\tilde\pi_{\beta,r,\zeta/\gamma}\rangle|\bar\mu\rangle
--   \quad\text{with complexity at most}\quad c\sqrt{\frac d{\beta\delta^2}}\cdot t\cdot\bigl(\log(2+t)\log(2+1/\epsilon)\bigr)^k ,
--   $$
--
--   where the read-out value $\bar\mu$ satisfies $|\mathbb E[\bar\mu]-\mu|\le\epsilon\tilde\sigma$ and $\mathrm{Var}[\bar\mu]\le(\tilde\sigma/t)^2$.
--
--   Run once per cooling stage with $t$ repetitions, this estimates the ratio $Z(\beta_{j+1})/Z(\beta_j)$ while restoring the state for the next stage.
--
--   Differences from the source:
--   - reading: Õ(√(d/(βδ²))·t·polylog(t, 1/ϵ)) → ∃ universal c > 0, k ∈ ℕ with W ≤ c·√(d/(βδ²))·t·(log(2 + t)·log(2 + 1/ϵ))^k; reason: paper.md decision 4
--   - encoding: complexity bound √(d/(βδ²)) (= +∞ at β = 0) → the bound multiplied by √β·δ, so at β = 0 only the action and the output guarantees are asserted; reason: Lean's division by zero returns 0
--   - encoding: δ ≤ min{1/(4βr), 1/(4096√(2dβ)), …} → 4βrδ ≤ 1, 4096√(2dβ)δ ≤ 1, …; reason: at β = 0 the paper's 1/(4βr) is +∞; the multiplicative form keeps β = 0 in the domain, whereas Lean's 1/0 = 0 would force δ ≤ 0
--   - reading: for sufficiently small ζ = ζ(listed parameters) > 0 we can construct a (canonical) transducer → ∃ ζ₀ > 0 depending only on the listed parameters, ∀ ζ ∈ (0, ζ₀], ∃ one transducer, ∀ admissible K; reason: paper.md decision 5; a canonical transducer does not depend on the input (Definition 2.10)
--   - reading: |π̃⟩ ⇝_V |π̃⟩|µ̄⟩ with E[µ̄], Var[µ̄] → |π̃⟩ ⊗ |0⟩ ⇝ |π̃⟩ ⊗ φ_K on an output register (answer and garbage); µ̄ = val(i) for the measured answer i, val fixed before K; E and Var under |φ_K(i,j)|²; reason: outputs of a canonical transducer are measured registers of a K-independent public space (paper.md decision 6)
--   - reading: states on K_ζ (public space ℂ^{K_ζ}) → states zero-extended to ℂ^{(RB_d)_ζ}; the public space may carry a further K-independent summand ℂ^e on which the stated states vanish; reason: Definition 2.10 forbids input-dependent public spaces; p.53 extends distributions by zero; the proof of Theorem 9.2 works on K_ζ ⊔ E (paper.md decision 6)
--   - encoding: σ ≤ σ̃ with σ² the variance → √(Var) ≤ σ̃; reason: σ is the square root of the variance
-- source:
--   Cornelissen, Apers, Gribling, Improved quantum volume estimation with transducers and amortized quantum walks, arXiv:2609.40217 (version of November 3, 2026, sha256 40d7b52d…), Theorem 10.2, p.68 (PDF p.70)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Query
import Definitions.Def_QVolTransducer_BiCanonical
import Definitions.Def_QVolTransducer_rejStat
import Definitions.Def_QVolTransducer_partitionFn
import Definitions.Def_QVolTransducer_IsPiecewiseLipschitz
import Definitions.Def_QVolTransducer_readMean

namespace QVolTransducer

open QAlgorithms

/-- **Non-destructive mean estimation over the rejection-sampled Gibbs state** (Cornelissen,
Apers, Gribling, *Improved quantum volume estimation with transducers and amortized quantum walks*,
arXiv:2609.40217 (version of November 3, 2026, sha256 40d7b52d…), Theorem 10.2, p.68 (PDF p.70)).

There are universal constants `c > 0` and `k ∈ ℕ` such that for all `d ≥ 1`, `R ≥ 1`, `β ≥ 0`,
`δ`, `0 < ϵ < 1`, `M > 0`, `L`, `h` and `σ̃ > 0` there is
`ζ₀ = ζ₀(d, R, β, δ, ϵ, M, L, h, σ̃) > 0` with the following property. Let `t ≥ 1`, `r ≥ 1`,
`0 < δ ≤ min{1/(4βr), 1/(4096√(2dβ)), 1/(4096√(d ln(20d/min{ϵ²/2²⁰, ϵ²/(2⁴¹t²)})))}`,
`0 < ζ ≤ ζ₀`, `γ = 1 − 1/(2d)`, let `X : RB_d → [0, M]` be piecewise `L`-Lipschitz on an
`h`-smooth partition, and let `m̃ ∈ ℝ`. Then there is one bidirectional canonical transducer `V`,
querying `O_{K,ζ}` and `O_{K,ζ/γ}`, with an output register and a readout, such that for every
convex body `B_d ⊆ K ⊆ RB_d` for which the mean `µ` and variance `σ²` of `X` over `π_{β,r}`
satisfy `σ ≤ σ̃` and `|µ − m̃| ≤ 17σ̃`:
`|π̃_{β,r,ζ/γ}⟩ ⇝_V |π̃_{β,r,ζ/γ}⟩|µ̄⟩` with complexity at most
`c √(d/(βδ²)) · t · (log(2+t) log(2+1/ϵ))^k`, where the read-out value `µ̄` satisfies
`|E[µ̄] − µ| ≤ ϵσ̃` and `Var[µ̄] ≤ (σ̃/t)²`.

**Formalization Note** The output `|π̃⟩|µ̄⟩` is the product state `|π̃⟩ ⊗ φ_K` with `φ_K` a state of
an output register `Fin (a+1) × Fin (g+1)` (answer and garbage), starting in `|0⟩`; `µ̄` is the
value `val(i)` of the measured answer `i`, with `val` fixed before `K`; `E[µ̄]` and `Var[µ̄]` are its
mean and variance under `|φ_K(i,j)|²`. `Õ(·polylog(t, 1/ϵ))` is read as a universal `c` and `k` with
`log(2+·)` factors. The complexity bound is stated multiplied by `√β δ`, so at `β = 0` (bound `+∞`)
only the action and the output guarantees are asserted. The public space may carry a further
`K`-independent summand. `ζ₀` depends on the printed parameters only (not on `t`, `r`, `X`, `m̃`). -/
theorem theorem_10_2 :
    ∃ c : ℝ, 0 < c ∧ ∃ k : ℕ, ∀ (d : ℕ) (R β δ ϵ M L : ℝ) (h : ℝ → ℝ) (σt : ℝ),
      ∃ ζ₀ : ℝ, 0 < ζ₀ ∧ ∀ t r : ℝ,
      1 ≤ d → 1 ≤ R → 0 < ϵ → ϵ < 1 → 1 ≤ t → 0 ≤ β → 1 ≤ r → 0 < δ →
      4 * β * r * δ ≤ 1 → 4096 * Real.sqrt (2 * d * β) * δ ≤ 1 →
      4096 * Real.sqrt (d * Real.log (20 * d /
        min (ϵ ^ 2 / 2 ^ 20) (ϵ ^ 2 / (2 ^ 41 * t ^ 2)))) * δ ≤ 1 →
      0 < M → 0 < σt →
      ∀ ζ : ℝ, 0 < ζ → ζ ≤ ζ₀ →
      ∀ X : EuclideanSpace ℝ (Fin d) → ℝ,
        (∀ x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) R, X x ∈ Set.Icc 0 M) →
        (∃ (n : ℕ) (parts : Fin n → Set (EuclideanSpace ℝ (Fin d))),
          IsPiecewiseLipschitz X (Metric.closedBall 0 R) L parts h) →
      ∀ mt : ℝ,
        ∃ (a g e n : ℕ)
          (V : BiCanonical ((Grid d (ζ / shrink d) R × (Fin (a + 1) × Fin (g + 1))) ⊕ Fin e)
            (Grid d ζ R ⊕ Grid d (ζ / shrink d) R) (Fin n))
          (val : Fin (a + 1) → ℝ),
          ∀ K : Set (EuclideanSpace ℝ (Fin d)), IsCompact K → Convex ℝ K →
            Metric.closedBall 0 1 ⊆ K → K ⊆ Metric.closedBall 0 R →
            Real.sqrt (gibbsVar (K ∩ Metric.closedBall 0 r) β X) ≤ σt →
            |gibbsMean (K ∩ Metric.closedBall 0 r) β X - mt| ≤ 17 * σt →
            ∃ (φ : EuclideanSpace ℂ (Fin (a + 1) × Fin (g + 1))) (w : EuclideanSpace ℂ _),
              TransducesWith (V.apply (twoGridOracle K ζ (ζ / shrink d) R))
                (embL (tensorVec (gridState (rejStat K β δ r ζ R)) (ket (0, 0))))
                (embL (tensorVec (gridState (rejStat K β δ r ζ R)) φ)) w ∧
              ‖w‖ ^ 2 * (Real.sqrt β * δ) ≤
                c * Real.sqrt d * t * (Real.log (2 + t) * Real.log (2 + 1 / ϵ)) ^ k ∧
              |readMean φ val - gibbsMean (K ∩ Metric.closedBall 0 r) β X| ≤ ϵ * σt ∧
              readVar φ val ≤ (σt / t) ^ 2 := by sorry

end QVolTransducer
