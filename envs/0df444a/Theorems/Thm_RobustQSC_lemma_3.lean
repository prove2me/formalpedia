-- Prove2me | Theorems.Thm_RobustQSC_lemma_3
-- name    : RobustQSC.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:54:12.762429+00:00
-- url     : https://prove2.me/theorems/6ac0e524-f2c9-4b03-ae61-10023aaebb18
-- title:
--   Lemma 3, p.25 — expectation bound $\mathbb E_{f\sim F_\mu}\mathrm{Avg}_{\hat f}[\widehat{fq}]\le\frac12+t$
-- statement:
--   For all $t>0$, for all $n$ large enough, with exponential probability over $\mu\sim\boldsymbol\mu$, for all fixed $\mu$-compatible $q$,
--
--   $$
--   \mathop{\mathbb E}_{f\sim F_\mu}\mathrm{Avg}_{\hat f}[\widehat{fq}]\le\frac12+t.
--   $$
--
--   This identifies the mean around which Theorem 5's concentration takes place: on the Fourier side a fixed $q$ passes the test about half the time.
--
--   Differences from the source:
--   - encoding: the middle term $\mathbb E_{f\sim F_\mu}[\frac1n\sum_iA^{(i)}]$ → omitted; reason: $\mathrm{Avg}_{\hat f}[\hat g]=\frac1n\sum_iA^{(i)}$ by definition (p.22)
--   - encoding: the expectation $\mathbb E_{f\sim F_\mu}$ → a Bochner integral, with integrability asserted in the conclusion; reason: the integrand is measurable and bounded; asserting it excludes the junk value of a non-integrable integrand
--   - reading: "exponential probability" → the outer measure of "the bound fails for some compatible $q$" is at most $e^{-c_0n}$, with $c_0$ and $n_0$ allowed to depend on $t$; reason: the printed quantifier order puts $t$ first
-- source:
--   Coladangelo, Li, Slote, Robust quantum state certification and uncertainty principles for total influence, arXiv:2607.27184 (sha256 09d2692e…), Lemma 3, p.25; A^{(i)}, p.22

import Definitions.Def_RobustQSC_dirichletOne
import Definitions.Def_RobustQSC_phaseLaw
import Definitions.Def_RobustQSC_avg
import Definitions.Def_RobustQSC_Compatible

namespace RobustQSC

open QAlgorithms MeasureTheory

/-- **Lemma 3.** For all `t > 0`, for all `n` large enough, with exponential probability over
`μ ∼ 𝛍`, for all fixed `μ`-compatible `q`, `E_{f∼F_μ} Avg_f̂[\widehat{fq}] ≤ ½ + t`.

Source: Coladangelo, Li, Slote, *Robust quantum state certification and uncertainty principles for
total influence*, arXiv:2607.27184 (sha256 09d2692e…), Lemma 3, p.25 (the middle term `E_{f∼F_µ}[(1/n)Σ_i A^{(i)}]` is the same
quantity: `Avg_f̂[ĝ] = (1/n)Σ_i A^{(i)}`, p.22).

**Formalization Note.**
1. `μ ∼ 𝛍` is `dirichletOne`, `f ∼ F_μ` is `phaseLaw μ`, `fq` is `ptMul f q`.
2. "Exponential probability": the `μ`-probability that the bound fails for **some** compatible
   `q` is at most `exp(−c₀ n)` for `n ≥ n₀`; `c₀` and `n₀` may depend on `t`.
3. The conclusion also asserts that the integrand is integrable, so that the Bochner integral is
   the expectation (it is bounded by `‖fq‖² = 1` and measurable). -/
theorem lemma_3 :
    ∀ t : ℝ, 0 < t → ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
      dirichletOne (Qubits n) {μ | ¬ ∀ q : Qubits n → ℂ, Compatible μ q →
          Integrable (fun f => avg (fourier f) (fourier (ptMul f q))) (phaseLaw μ) ∧
          ∫ f, avg (fourier f) (fourier (ptMul f q)) ∂(phaseLaw μ) ≤ 1 / 2 + t}
        ≤ ENNReal.ofReal (Real.exp (-(c₀ * n))) := by sorry

end RobustQSC
