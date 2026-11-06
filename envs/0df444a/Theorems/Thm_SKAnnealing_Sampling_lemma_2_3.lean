-- Prove2me | Theorems.Thm_SKAnnealing_Sampling_lemma_2_3
-- name    : SKAnnealing.Sampling.lemma_2_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:18:16.011198+00:00
-- url     : https://prove2.me/theorems/65e11c92-a8a9-442a-ba6b-664da33b93ee
-- title:
--   Lemma 2.3, p. 11 — simulated annealing from weak Poincaré inequalities: $d_{\mathrm{TV}}(\nu,\mu_{\beta H})\le O\big(L(e^{-m/(2\rho)}+\sqrt\varepsilon)\big)$
-- statement:
--   Let $H:\{\pm1\}^N\to\mathbb R$ be a Hamiltonian with maximum $H_{\max}$ and minimum $H_{\min}$, and $\mu_{\beta H}(x)\propto e^{\beta H(x)}$. Let $0=\beta_0<\beta_1<\dots<\beta_L=\beta$ be a schedule.
--
--   **Lemma 2.3 (Simulated annealing from weak Poincaré inequalities).** There are universal constants $c>0$ and $C>0$ such that the following holds. Suppose that, for some $\rho>0$ and $\varepsilon\ge0$, each $\mu_{\beta_jH}$, $j\in[L]$, satisfies a $(\rho,\varepsilon)$-weak Poincaré inequality, and that for each $j\in[L]$
--   $$\beta_j-\beta_{j-1}\le\frac{c}{H_{\max}-H_{\min}} .$$
--   Starting from a uniformly random initialization, run $m$ Glauber updates at each inverse temperature $\beta_j$, $j=1,\dots,L$. Then the output distribution $\nu$ satisfies, for every $m$,
--   $$d_{\mathrm{TV}}(\nu,\mu_{\beta H})\le C\,L\Big(e^{-\frac m{2\rho}}+\sqrt\varepsilon\Big).$$
--
--   This is the generic annealing guarantee ([HMRW24, Theorem 4.13]) that turns weak Poincaré inequalities at all temperatures of the schedule into a sampling guarantee; Theorem 1.1 applies it with $H(\sigma)=\frac12\langle\sigma,W\sigma\rangle$.
--
--   Differences from the source:
--   - reading: each µ_{β_jH} satisfies a (ρ, ε)-weak Poincaré inequality → the inequality is assumed for j ∈ [L] = {1, …, L} only, not at β₀ = 0; reason: "each" is ambiguous between {0, …, L} and [L]; the weaker hypothesis gives the stronger lemma (reading R10)
--   - encoding: β_j − β_{j−1} ⩽ c/(H_max − H_min) → (β_j − β_{j−1})·(H_max − H_min) ≤ c; reason: the same condition when H_max > H_min; for constant H the printed c/0 is read as +∞ (no condition), which Lean's c/0 = 0 would turn into an unsatisfiable hypothesis
--   - reading: some sufficiently small constant c > 0; O(·) → ∃ universal c > 0 and C > 0, before N, H, L, the schedule, ρ, ε and m; reason: the constants of the lemma do not depend on its data (reading R3)
--   - encoding: a schedule 0 = β₀ < ⋯ < β_L → b : ℕ → ℝ with b 0 = 0, strictly increasing on {0, …, L}; values beyond L unused; reason: a sequence indexed by ℕ; only its first L + 1 values enter
--   - reading: the standard Dirichlet form ℰ(f, f) and ‖f‖_∞ in display (2) → ℰ(f, f) = N^{−1} Σ_i E_µ[(f − P_i f)²] (the discrete Glauber chain of Definition 2.1), ‖f‖_∞ the maximum of |f| on the support of µ; reason: the (O(N), ·) constants fit the discrete-time chain; on the full-support Gibbs laws of the paper the support is all of {±1}^N (reading R7)
--   - encoding: a (ρ, ε)-weak Poincaré inequality → hypotheses 0 < ρ and 0 ≤ ε; reason: ρ is a Poincaré-type constant and ε an error level; for ρ ≤ 0 or ε < 0 display (2) is not the inequality the paper means (with ε < 0 it is stronger than a Poincaré inequality and √ε is undefined)
-- source:
--   Du, Huang, Mohanty, Rajaraman, Sampling from the Sherrington–Kirkpatrick Model up to Criticality, arXiv:2610.17717 (PDF of October 29, 2026), Lemma 2.3, p. 11 (PDF p. 13)

import Mathlib
import Definitions.Def_CriticalSK
import Definitions.Def_SKAnnealing_Sampling_lawMean
import Definitions.Def_SKAnnealing_Sampling_glauberKernel
import Definitions.Def_SKAnnealing_Sampling_IsWeakPoincare
import Definitions.Def_SKAnnealing_Sampling_gibbsOf
import Definitions.Def_SKAnnealing_Sampling_annealRun

open OAI.CriticalSK MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace SKAnnealing.Sampling

/-- **Lemma 2.3** (simulated annealing from weak Poincaré inequalities). Let `0 = β_0 < β_1 < ⋯ < β_L = β`.
Suppose each `µ_{β_j H}` satisfies a `(ρ, ε)`-weak Poincaré inequality, and for each `j ∈ [L]` and some sufficiently
small constant `c > 0`, `β_j − β_{j−1} ≤ c/(H_max − H_min)`. Starting from a uniformly random initialization, run
`m` Glauber updates at each inverse temperature `β_j`. Then the output distribution `ν` satisfies
`d_TV(ν, µ_{βH}) ≤ O(L(e^{−m/(2ρ)} + √ε))`.

Du, Huang, Mohanty, Rajaraman, *Sampling from the Sherrington–Kirkpatrick Model up to Criticality*, arXiv:2610.17717 (PDF of October 29, 2026), Lemma 2.3, p. 11 (PDF p. 13).

**Formalization Note** `c > 0` and the constant `C` of `O(·)` are universal. Reading R10: the weak Poincaré inequality is
assumed for `j ∈ [L]` (not at `β_0 = 0`). The gap condition is written `(β_j − β_{j−1})(H_max − H_min) ≤ c`, which is
the printed one when `H_max > H_min` and imposes nothing when `H` is constant (the printed `c/0` read as `+∞`). The
schedule is `b : ℕ → ℝ`, used on `{0, …, L}`. -/
theorem lemma_2_3 :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (N : ℕ) (H : Spin N → ℝ) (L : ℕ) (b : ℕ → ℝ) (ρ ε : ℝ),
        b 0 = 0 → StrictMonoOn b (Set.Iic L) → 0 < ρ → 0 ≤ ε →
        (∀ j : ℕ, 1 ≤ j → j ≤ L → IsWeakPoincare (gibbsOf H (b j)) ρ ε) →
        (∀ j : ℕ, 1 ≤ j → j ≤ L → (b j - b (j - 1)) * (hMax H - hMin H) ≤ c) →
        ∀ m : ℕ, lawTV (annealOutputOf H b L m) (gibbsOf H (b L))
          ≤ C * L * (Real.exp (-(m / (2 * ρ))) + Real.sqrt ε) := by sorry

end SKAnnealing.Sampling
