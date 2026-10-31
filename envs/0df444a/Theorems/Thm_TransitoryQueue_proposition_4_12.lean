-- Prove2me | Theorems.Thm_TransitoryQueue_proposition_4_12
-- name    : TransitoryQueue.proposition_4_12
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:01:56.804451+00:00
-- url     : https://prove2.me/theorems/84410cc9-fb2b-4720-a68d-1c7eff384ee3
-- title:
--   Proposition 4.12 (corrected: pathwise Lévy modulus replaces the false tail bound)
-- statement:
--   Let $P$ be a probability measure.
--
--   1. If $B$ is a standard Brownian motion, then almost surely, for every $D>0$ there is $C$ such that for all $a,b\in[0,D]$,
--   $$|B_a-B_b|\le C\sqrt{|a-b|\bigl(1+\log^+(1/|a-b|)\bigr)}.$$
--   2. If $Y$ is a Brownian bridge, then almost surely there is $C$ such that the same bound holds for all $a,b\in[0,1]$.
--
--   Here $\log^+y=\max(0,\log y)$. Consequently, for arbitrary time processes $\Xi_n,\xi_n$ with values in $[0,D]$ — dependent on $B$ or not — $\sup_s|B_{\Xi_n(s)}-B_{\xi_n(s)}|$ is at most $C\,h(\sup_s|\Xi_n(s)-\xi_n(s)|)$ with $h(\delta)=\sqrt{\delta(1+\log^+(1/\delta))}$. This is what the proofs of Theorems 2.8 and 2.11 need from Proposition 4.12.
--
--   Differences from the source:
--   - correction: P(sup_{s∈[0,L_n]} |B_{Ξ_n(s)} − B_{ξ_n(s)}| > C √(log((c_{ξ_n} L_n) ∨ n))/n^{1/4} + x) ≤ 2 e^{−x²/(2υ_n²)}, υ_n² = sup_s E|Ξ_n(s) − ξ_n(s)| (48) → almost surely, |B_a − B_b| ≤ C √(|a−b|(1 + log⁺(1/|a−b|))) on [0, D] (and the same for a Brownian bridge on [0, 1]), with no condition on the time processes; reason: (48) is false: with L_n = 1, ξ_n ≡ 0, Ξ_n ≡ R_n, P(R_n = 1) = e^{−n} = 1 − P(R_n = 0), B independent of R_n, Assumptions 4.1–4.3 and 4.9 hold and υ_n² = e^{−n}, but at x = 1 the left side is at least a·e^{−n} (a > 0 fixed) while the right side is 2exp(−e^n/2); the paper also applies it in (132) and Lemma 7.2 where Ξ_n depends on B
--   - encoding: B_t for t ∈ [0, L_n] → B at a, b : ℝ≥0 with a, b ≤ D, for every D > 0; reason: Mathlib's Brownian motion has time in ℝ≥0
-- source:
--   Chakraborty and Honnappa, Strong Embeddings for Transitory Queueing Models, arXiv:1906.06740v1, Proposition 4.12, eq. (48), p.21

import Mathlib
import Definitions.Def_TransitoryQueue_IsBrownianBridge
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace TransitoryQueue

/-- **Proposition 4.12, corrected: Lévy's modulus of continuity, pathwise.** Let `P` be a
probability measure.

1. If `B` is a standard Brownian motion, then almost surely, for every `D > 0` there is `C` with
   `|B_a - B_b| ≤ C √(|a - b| (1 + log⁺(1/|a - b|)))` for all `a, b ∈ [0, D]`.
2. If `Y` is a Brownian bridge, then almost surely there is `C` with the same bound for all
   `a, b ∈ [0, 1]`.

Consequently `|B_{Ξ(s)} - B_{ξ(s)}|` is controlled by the modulus at `sup_s |Ξ(s) - ξ(s)|` for
arbitrary (possibly dependent) time processes `Ξ`, `ξ` with values in `[0, D]`.
Chakraborty and Honnappa, *Strong Embeddings for Transitory Queueing Models*, arXiv:1906.06740v1, Proposition 4.12, p.21, eq. (48), corrected.

**Formalization Note** The printed (48) bounds the tail of `sup_s |B_{Ξ_n(s)} - B_{ξ_n(s)}|` by
`2 e^{-x²/(2υ_n²)}` with `υ_n² = sup_s E|Ξ_n(s) - ξ_n(s)|`; this is false (a time process equal to
`1` with probability `e^{-n}` and `0` otherwise, independent of `B`, violates it), and the paper
applies it where `Ξ_n` depends on `B`. The pathwise modulus needs neither independence nor a law
for `Ξ`. `log⁺ y = max 0 (log y)`; at `a = b` the bound is `0`. -/
theorem proposition_4_12 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] :
    (∀ B : ℝ≥0 → Ω → ℝ, IsBrownianReal B P →
      ∀ᵐ ω ∂P, ∀ D : ℝ≥0, 0 < D → ∃ C : ℝ, ∀ a b : ℝ≥0, a ≤ D → b ≤ D →
        |B a ω - B b ω| ≤ C * Real.sqrt (|(a : ℝ) - b| *
          (1 + max 0 (Real.log (1 / |(a : ℝ) - b|))))) ∧
    (∀ Y : ℝ → Ω → ℝ, IsBrownianBridge Y P →
      ∀ᵐ ω ∂P, ∃ C : ℝ, ∀ a b : ℝ, a ∈ Set.Icc (0 : ℝ) 1 → b ∈ Set.Icc (0 : ℝ) 1 →
        |Y a ω - Y b ω| ≤ C * Real.sqrt (|a - b| * (1 + max 0 (Real.log (1 / |a - b|))))) := by sorry

end TransitoryQueue
