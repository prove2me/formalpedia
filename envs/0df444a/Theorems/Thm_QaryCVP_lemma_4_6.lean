-- Prove2me | Theorems.Thm_QaryCVP_lemma_4_6
-- name    : QaryCVP.lemma_4_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T10:01:04.032189+00:00
-- url     : https://prove2.me/theorems/0afc6df1-882b-444b-abd7-0cfe0997338a
-- title:
--   Lemma 4.6 — $r=\lceil Cn\rceil$ attempts give $\|\bar w(s)\|\le(c-\beta)\sqrt n$ for every $s$ with probability $1-2^{-\Omega(n)}$
-- statement:
--   Fix constants $0<\beta<1$, $p\in(0,1)$, $c>\beta$, $D>0$. There is a rational $C>0$, depending only on $p,\beta,c,D$, with the following property. Let $n\ge1$, $m\ge0$, $q\ge2$ with $\delta\le D$ and fix $H\in(\mathbb Z/q\mathbb Z)^{m\times n}$. Suppose that for every $s\in(\mathbb Z/q\mathbb Z)^m$ a randomized attempt returns $\bot$ or an integer vector $w$ with $Hw=s$, $\|w\|^2\le\beta n$, and satisfies
--
--   $$\Pr[\text{success}]\ge p/2,\qquad\|\mathbb E[w\mid\text{success}]\|\le\frac{c-\beta}{8}\sqrt n.$$
--
--   Run $r=\lceil Cn\rceil$ independent attempts for each $s$, using the same random bits for corresponding attempts when different $s$ are compared. For sufficiently large $n$, with probability at least $1-2^{-\Omega(n)}$ over these bits, every $s$ has a successful attempt and the average $\bar w(s)$ of its successful outputs satisfies $\|\bar w(s)\|\le(c-\beta)\sqrt n$.
--
--   **Formalization Note** An attempt is a function of $s$ and its randomness $\omega\sim\mu$ on an arbitrary probability space with measurable outcome events; the $r$ attempts use independent copies $\omega_1,\dots,\omega_r$ shared by all $s$, so "every $s$" sits inside the probability.
--
--   Differences from the source:
--   - generalization: a randomized attempt using random bits → a function att s ω on an arbitrary probability space (Ω, μ) with measurable outcome events; reason: covers fair bits as a special case
--   - reading: for sufficiently large n, with probability at least 1 − 2^{−Ω(n)} → ∃ c′ > 0, N, chosen with C before n, m, q, H and the attempt; reason: p.12 convention; constants depend only on p, β, c, D
--   - encoding: probability of an event of the coin tape → fair-coin measure of the event, with its measurability a clause of the conclusion; reason: the event is defined from a program run; measurability makes the probability meaningful
-- source:
--   Kim, Kwon, Lee, Lee, Fast Provable Algorithms for Approximate CVP and Exact SVP on Random q-ary Lattices, STOC 2027 submission manuscript (sha256 9aeb2ff4…ab4), Lemma 4.6, p.38

import Mathlib
import Definitions.Def_QaryCVP_qaryLattice
import Definitions.Def_QaryCVP_corrAttempt
import Definitions.Def_QaryCVP_alg3

open MeasureTheory ProbabilityTheory

namespace QaryCVP

/-- **Lemma 4.6** (repeated attempts). Kim, Kwon, Lee, Lee, STOC 2027 submission manuscript
(sha256 9aeb2ff4…ab4), Lemma 4.6, p.38.

Fix constants `0 < β < 1`, `p ∈ (0, 1)`, `c > β`, `D > 0`. There is a rational `C > 0`, depending
only on `p, β, c, D`, such that: let `n ≥ 1`, `m ≥ 0`, `q ≥ 2` with `δ ≤ D` and fix
`H ∈ (Z/qZ)^{m×n}`; suppose that for every `s ∈ (Z/qZ)^m` a randomized attempt returns `⊥` or an
integer vector `w` with `Hw = s`, `‖w‖² ≤ βn`, and satisfies `Pr[success] ≥ p/2` and
`‖E[w | success]‖ ≤ ((c − β)/8)√n`. Run `r = ⌈Cn⌉` independent attempts for each `s`, using the same
random bits for corresponding attempts when different `s` are compared. For sufficiently large
`n`, with probability at least `1 − 2^{−Ω(n)}` over these bits, every `s` has a successful attempt
and the average `w̄(s)` of its successful outputs satisfies `‖w̄(s)‖ ≤ (c − β)√n`.

**Formalization Note.** An attempt is a function `att s ω` of the right-hand side and the attempt's
randomness `ω ∼ μ` (measurable outcome events); the `r` attempts use independent copies
`ω₁, …, ω_r`, the same for every `s`, so the event quantifies `∀ s` inside. `2^{−Ω(n)}` is
`∃ c' > 0, N`, chosen with `C` before `n, m, q, H` and the attempt (R4). The event is measurable
(a clause of the conclusion). -/
theorem lemma_4_6 (β p c D : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (hp0 : 0 < p) (hp1 : p < 1)
    (hcβ : β < c) (hD : 0 < D) :
    ∃ C : ℚ, 0 < C ∧ ∃ c' : ℝ, 0 < c' ∧ ∃ N : ℕ, ∀ n m q : ℕ, N ≤ n → 1 ≤ n → 2 ≤ q →
      density q m n ≤ D →
      ∀ (H : Matrix (Fin m) (Fin n) (ZMod q)) {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
        [IsProbabilityMeasure μ] (att : (Fin m → ZMod q) → Ω → Option (Fin n → ℤ)),
        (∀ s (o : Option (Fin n → ℤ)), MeasurableSet {ω | att s ω = o}) →
        (∀ s ω w, att s ω = some w →
          H.mulVec (fun j => (w j : ZMod q)) = s ∧ sqNormZ w ≤ β * n) →
        (∀ s, p / 2 ≤ succProb μ (att s) ∧
          condMeanNorm μ (att s) ≤ (c - β) / 8 * Real.sqrt n) →
        let E : Set (Fin (rOf C n) → Ω) := {ωs | ∀ s : Fin m → ZMod q,
          (∃ i, (att s (ωs i)).isSome) ∧
            eucNorm (succAvg (att s) ωs) ≤ (c - β) * Real.sqrt n}
        MeasurableSet E ∧
          1 - (2 : ℝ) ^ (-c' * n) ≤ (Measure.pi (fun _ : Fin (rOf C n) => μ) E).toReal := by sorry

end QaryCVP
