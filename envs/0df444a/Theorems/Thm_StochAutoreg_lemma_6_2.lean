-- Prove2me | Theorems.Thm_StochAutoreg_lemma_6_2
-- name    : StochAutoreg.lemma_6_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:12:45.538423+00:00
-- url     : https://prove2.me/theorems/675fe722-1d04-499d-86fb-4b0af2673374
-- title:
--   Lemma 6.2 — sign testing: $\mathrm{KL}\le1/50$ forces $D/16$ errors with probability $>1/3$
-- statement:
--   Let $D\ge1$ and let $\omega^{(j)}$ denote $\omega\in\{-1,1\}^D$ with its $j$th sign flipped. Suppose the law $\mathbb P_\omega$ of the training sample satisfies $\mathrm{KL}(\mathbb P_\omega\|\mathbb P_{\omega^{(j)}})\le1/50$ for every $\omega$ and $j\in[D]$. Then any estimator $\hat\omega\in\{-1,1\}^D$ makes at least $D/16$ coordinate errors with probability greater than $1/3$ for some $\omega$:
--
--   $$\exists\omega:\quad\Pr\bigl\{\#\{j:\hat\omega_j\ne\omega_j\}\ge D/16\bigr\}>\frac13.$$
--
--   This is the testing tool for the lower bounds of Section 7. The inequality is strict, which excludes a learner succeeding with probability exactly $2/3$.
--
--   Differences from the source:
--   - generalization: the learner's independent random bits → independent randomness from an arbitrary probability space (Ω, ν), and a sample in an arbitrary measurable space; reason: it specializes to the source, and in particular to the seed law on [0,1]
--   - encoding: an estimator → a map whose fibers over sign vectors are measurable; reason: the target space is finite and discrete, so this is measurability
--   - encoding: KL between sample laws, and "at least D/16" → Mathlib's klDiv in ℝ≥0∞, and the real comparison D ≤ 16·#errors; reason: Lean representation; natural-number division is avoided
-- source:
--   Doron-Arad–Mehalel–Mossel, Stochastic Autoregressive Learning, arXiv:2608.07224, Lemma 6.2, p.12

import Mathlib
open MeasureTheory

namespace StochAutoreg

/-- **Lemma 6.2** (sign testing). Let `D ≥ 1`, and let `ω^{(j)}` be `ω ∈ {-1,1}^D` with its `j`th sign flipped. If the law `P_ω` of
the training sample satisfies `KL(P_ω‖P_{ω^{(j)}}) ≤ 1/50` for every `ω` and `j`, then any estimator `ω̂ ∈ {-1,1}^D` makes at least
`D/16` coordinate errors with probability greater than `1/3` for some `ω`. Doron-Arad–Mehalel–Mossel, *Stochastic Autoregressive Learning*, arXiv:2608.07224, Lemma 6.2, p.12.

**Formalization Note.** The sample lies in any measurable space, and the estimator may use independent randomness from any
probability space `(Ω, ν)`, as the proof's "the learner's independent random bits". "At least `D/16`" is the real comparison
`D ≤ 16 · #errors`. The KL is Mathlib's `InformationTheory.klDiv`. -/
theorem lemma_6_2 {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω] (D : ℕ) (hD : 1 ≤ D)
    (Pw : (Fin D → ℤˣ) → Measure S) [∀ ω, IsProbabilityMeasure (Pw ω)]
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    (hKL : ∀ (ω : Fin D → ℤˣ) (j : Fin D),
      InformationTheory.klDiv (Pw ω) (Pw (Function.update ω j (-ω j))) ≤ ENNReal.ofReal (1 / 50))
    (est : S × Ω → Fin D → ℤˣ) (hest : ∀ ω', MeasurableSet (est ⁻¹' {ω'})) :
    ∃ ω : Fin D → ℤˣ,
      ENNReal.ofReal (1 / 3) < ((Pw ω).prod ν)
        {w | (D : ℝ) ≤ 16 * (((Finset.univ.filter fun j => est w j ≠ ω j).card : ℕ) : ℝ)} := by sorry

end StochAutoreg
