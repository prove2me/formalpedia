-- Prove2me | Theorems.Thm_ProdMixedTomo_Supplement_theorem_5_1
-- name    : ProdMixedTomo.Supplement.theorem_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T22:33:50.550285+00:00
-- url     : https://prove2.me/theorems/a41ebe3d-e934-46cd-b32c-94ced8194ed2
-- title:
--   Theorem 5.1 — non-adaptive single-copy algorithms need $\exp(n^c)$ copies
-- statement:
--   There are $c>0$ and $n_0$ such that for every $n\ge n_0$ and every $N$ the following holds. Let $\mathcal A$ be any non-adaptive single-copy measurement algorithm on $n$ qubits using $N$ copies (shared randomness drawn first, then an arbitrary POVM on each copy chosen from the randomness only, then an arbitrary randomized decoder with output $\hat\pi\in\mathcal M_n$). If for every $n$-qubit density matrix $\rho$ with $\mathrm{opt}(\rho)=\inf_{\pi\in\mathcal M_n}d_{\mathrm{tr}}(\pi,\rho)\le n^{-c}$ the algorithm satisfies
--   $$
--   \Pr\bigl[d_{\mathrm{tr}}(\rho,\hat\pi)\le 1-e^{-n^c}\bigr]\ \ge\ e^{-n^c},
--   $$
--   then
--   $$
--   N\ \ge\ e^{n^c}.
--   $$
--   So without adaptivity even a nontrivial trace-distance guarantee with exponentially small success probability needs exponentially many copies, on states that are polynomially close to product; the second, adaptive round of the algorithm for the goal (Corollary 3.3) cannot be removed.
--
--   Differences from the source:
--   - encoding: "any algorithm using only non-adaptive single-copy measurements" → any NonAdaptiveAlg n N: a probability space of seeds, for each copy a POVM with finitely many outcomes on the whole n-qubit space chosen measurably from the seed, and a measurable decoder of the seed and outcomes; reason: every finite-dimensional POVM is a randomization of finite-outcome POVMs followed by post-processing, and all randomness independent of the outcomes can be drawn first, so this is the full class
--   - encoding: "outputs π̂ ∈ M_n" → the decoder outputs Bloch vectors c₁, …, c_n with ‖cⱼ‖ ≤ 1 and π̂ = ⊗ⱼ ½(I + cⱼ·σ); reason: these are exactly the elements of M_n
--   - encoding: Pr[d_tr(ρ, π̂) ≤ 1 − exp(−n^c)] → succProb: integral over the seed of the sum over outcome strings of ∏ᵢ Re tr(ρ Mᵢ(ω)(oᵢ)) times the indicator of the event; reason: Born rule on ρ^{⊗N}, one measurement per copy
--   - encoding: "requires at least exp(n^c) copies" → the success hypothesis for every such ρ implies exp(n^c) ≤ N; reason: the contrapositive form of "requires"
-- source:
--   Arulandu, Diakonikolas, Kane, Li, Agnostic Product Mixed State Tomography via Robust Statistics, arXiv:2510.08472 (manuscript of Nov. 3, 2026, sha256 6c87a7ba…), Theorem 5.1, p.34 (PDF p.36); proof, pp.37–38 (PDF pp.39–40)

import Mathlib
import Definitions.Def_ProdMixedTomo_States
import Definitions.Def_ProdMixedTomo_TraceDistance
import Definitions.Def_ProdMixedTomo_Supplement_NonAdaptiveAlg

namespace ProdMixedTomo.Supplement

/-- Arulandu, Diakonikolas, Kane, Li, *Agnostic Product Mixed State Tomography via Robust Statistics*, arXiv:2510.08472 (manuscript of Nov. 3, 2026, sha256 6c87a7ba…), Theorem 5.1, p.34 (PDF p.36). For some `c > 0` and all sufficiently large `n`, any
algorithm using only non-adaptive single-copy measurements which for every `n`-qubit state `ρ`
with `opt(ρ) ≤ n^{−c}` outputs `π̂ ∈ M_n` satisfying `Pr[d_tr(ρ, π̂) ≤ 1 − exp(−n^c)] ≥ exp(−n^c)`
requires at least `exp(n^c)` copies.

**Formalization Note.** `opt(ρ)` is the base `optM` (distance to `M_n`). The algorithm class is
`NonAdaptiveAlg n N`: shared randomness drawn first, then an arbitrary POVM on each copy (any
finite number of outcomes, entangled across the `n` qubits allowed) chosen from the seed only,
then an arbitrary measurable randomized decoder with output in `M_n`; no running-time bound. The
same `c` in all four places; `n^c` is the real power. -/
theorem theorem_5_1 :
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ (N : ℕ) (A : NonAdaptiveAlg n N),
      (∀ ρ : QMat n, IsDensity ρ → optM ρ ≤ (n : ℝ) ^ (-c) →
        ENNReal.ofReal (Real.exp (-(n : ℝ) ^ c)) ≤
          succProb A ρ (1 - Real.exp (-(n : ℝ) ^ c))) →
      Real.exp ((n : ℝ) ^ c) ≤ N := by sorry

end ProdMixedTomo.Supplement
