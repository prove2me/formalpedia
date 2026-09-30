-- Prove2me | Theorems.Thm_UnderstandingML_srm_bound
-- name    : UnderstandingML.srm_bound
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T03:47:58.493139+00:00
-- url     : https://prove2.me/theorems/f95ebc65-8c1c-44f8-85b2-1ffb44428882
-- title:
--   Theorem 7.4: with probability ≥ 1 − δ, |L_D(h) − L_S(h)| ≤ εₙ(m, w(n)δ) simultaneously for every n and h ∈ Hₙ
-- statement:
--   **Theorem 7.4.** Let $w : \mathbb{N} \to [0,1]$ be a function such that $\sum_n w(n) \le 1$. Let $H$ be a hypothesis class that can be written as $H = \bigcup_n H_n$, where for each $n$, $H_n$ satisfies the uniform convergence property with a sample complexity function $m^{UC}_{H_n}$. Let $\epsilon_n$ be as defined in Equation (7.1). Then for every $\delta \in (0,1)$ and distribution $D$, with probability of at least $1-\delta$ over the choice of $S \sim D^m$, the following bound holds simultaneously for every $n$ and $h \in H_n$: $|L_D(h) - L_S(h)| \le \epsilon_n(m, w(n)\cdot\delta)$.
--
--   Formally: the $D^m$-probability that for some $n$ with $w(n) > 0$ at which $\epsilon_n(m, w(n)\delta)$ is defined some $h \in H_n$ has $|L_D(h) - L_S(h)| > \epsilon_n(m, w(n)\delta)$ is at most $\delta$; the condition $\sum_n w(n) \le 1$ is stated on partial sums.
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §7.2 pp. 86-87, Theorem 7.4 with its proof

import Definitions.Def_UnderstandingML_Nonuniform

open MeasureTheory

namespace UnderstandingML

/-- **Theorem 7.4** (p. 86). Let `w : ℕ → [0,1]` be a function such that `∑ₙ w(n) ≤ 1`. Let
`H = ⋃ₙ Hₙ`, where each `Hₙ` satisfies the uniform convergence property with a sample
complexity function `m^{UC}_{Hₙ}`, and let `εₙ` be as in Equation (7.1). Then for every
`δ ∈ (0,1)` and distribution `D`, with probability of at least `1 − δ` over the choice of
`S ∼ D^m`, the following holds simultaneously for every `n` and `h ∈ Hₙ`:
`|L_D(h) − L_S(h)| ≤ εₙ(m, w(n)·δ)`. The bound is asserted for the indices `n` with
`w(n) > 0` at which `εₙ(m, w(n)·δ)` is defined (the set in (7.1) is nonempty); the sum
condition is stated on the partial sums. -/
theorem srm_bound {Z : Type*} [MeasurableSpace Z] {Hyp : Type*} (loss : Hyp → Z → ℝ)
    (Hn : ℕ → Set Hyp) (mUC : ℕ → ℝ → ℝ → ℕ)
    (hUC : ∀ n, HasUniformConvergenceWith loss (Hn n) (mUC n)) (w : ℕ → ℝ)
    (hw : ∀ n, 0 ≤ w n ∧ w n ≤ 1) (hsum : ∀ N, ∑ n ∈ Finset.range N, w n ≤ 1) {δ : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (D : Measure Z) [IsProbabilityMeasure D] (m : ℕ) :
    iidLaw D m {S | ∃ n, 0 < w n ∧ RateDefined (mUC n) m (w n * δ) ∧
        ∃ h ∈ Hn n, epsRate (mUC n) m (w n * δ) < |risk loss D h - empRisk loss S h|} ≤
      ENNReal.ofReal δ := by sorry

end UnderstandingML
