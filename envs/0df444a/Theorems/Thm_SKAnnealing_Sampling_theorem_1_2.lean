-- Prove2me | Theorems.Thm_SKAnnealing_Sampling_theorem_1_2
-- name    : SKAnnealing.Sampling.theorem_1_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:17:34.14446+00:00
-- url     : https://prove2.me/theorems/3fcd6d2f-fa15-4a7b-93fb-188e60dbc333
-- title:
--   Theorem 1.2, p. 2 — with probability $1-N^{-a}$ the SK measure satisfies an $(O(N),N^{-a})$-weak Poincaré inequality (uniformly in $\beta^\prime\in[0,\beta]$)
-- statement:
--   Let $W\sim\mathrm{GOE}(N)$ and let $\mu_{\beta W}(\sigma)\propto\exp\big(\frac\beta2\langle\sigma,W\sigma\rangle\big)$ be the SK model on $\{\pm1\}^N$.
--
--   **Theorem 1.2.** Let $0<\beta<1$ and $a>0$ be constants. There are $C>0$ and $N_0$ such that for every $N\ge N_0$ and **every** $\beta'\in[0,\beta]$,
--   $$\Pr_W\Big[\mu_{\beta'W}\text{ does not satisfy a }(CN,\,N^{-a})\text{-weak Poincaré inequality}\Big]\le N^{-a}.$$
--
--   For $\beta'=\beta$ this is the printed Theorem 1.2. The uniformity in $\beta'$ is what the proof of Theorem 1.1 uses when it takes "a union bound over temperatures": every inverse temperature of the annealing schedule lies in $[0,\beta]$.
--
--   Differences from the source:
--   - generalization: the SK model µ_{βW} at the fixed β → µ_{β′W} for every β′ ∈ [0, β], with one C and one N₀; reason: the proof of Theorem 1.1 (p. 13) applies Theorem 1.2 at every temperature of the schedule and takes a union bound, which needs this uniformity; β′ = β gives the printed theorem (reading R9)
--   - encoding: with probability at least 1 − N^{−a}; O(N) → for every N ≥ N₀ the failure event has measure ≤ N^{−a} (constant 1 kept); O(N) is C·N with C > 0; reason: asymptotic in N; written as a bound on the bad set (readings R3, R4)
--   - reading: the standard Dirichlet form ℰ(f, f) and ‖f‖_∞ in display (2) → ℰ(f, f) = N^{−1} Σ_i E_µ[(f − P_i f)²] (the discrete Glauber chain of Definition 2.1), ‖f‖_∞ the maximum of |f| on the support of µ; reason: the (O(N), ·) constants fit the discrete-time chain; on the full-support Gibbs laws of the paper the support is all of {±1}^N (reading R7)
--   - encoding: W ∼ GOE(N), a symmetric matrix with diagonal entries → the off-diagonal entries W_{ik}, i < k, iid N(0, 1/N) (OAI.CriticalSK.disorderLaw); no diagonal; reason: σ_i² = 1, so the diagonal only adds a constant to the Hamiltonian and changes no Gibbs measure, kernel or covariance (reading R8)
-- source:
--   Du, Huang, Mohanty, Rajaraman, Sampling from the Sherrington–Kirkpatrick Model up to Criticality, arXiv:2610.17717 (PDF of October 29, 2026), Theorem 1.2, p. 2 (PDF p. 4); its use in the proof of Theorem 1.1, p. 13

import Mathlib
import Definitions.Def_CriticalSK
import Definitions.Def_SKAnnealing_Sampling_lawMean
import Definitions.Def_SKAnnealing_Sampling_glauberKernel
import Definitions.Def_SKAnnealing_Sampling_IsWeakPoincare

open OAI.CriticalSK MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace SKAnnealing.Sampling

/-- **Theorem 1.2**, uniformly over the inverse temperatures `β' ∈ [0, β]`. Let `0 < β < 1` and `a > 0`. With
probability at least `1 − N^{−a}` over `W ∼ GOE(N)`, the SK model `µ_{βW}` satisfies an `(O(N), N^{−a})`-weak
Poincaré inequality.

Du, Huang, Mohanty, Rajaraman, *Sampling from the Sherrington–Kirkpatrick Model up to Criticality*, arXiv:2610.17717 (PDF of October 29, 2026), Theorem 1.2, p. 2 (PDF p. 4).

**Formalization Note** Reading R9 (generalization): one constant `C` and one `N₀` serve every `β' ∈ [0, β]`; the proof
of Theorem 1.1 (p. 13, "take a union bound over temperatures") needs this uniformity, and `β' = β` is the printed
theorem. `O(N)` is `C · N` with `C > 0` (R3); `N ≥ N₀` (R4). The weak Poincaré inequality is display (2) with the
Glauber Dirichlet form (R7). -/
theorem theorem_1_2 :
    ∀ β : ℝ, 0 < β → β < 1 → ∀ a : ℝ, 0 < a →
      ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ β' : ℝ, 0 ≤ β' → β' ≤ β →
        disorderLaw N {W | ¬ IsWeakPoincare (gibbs (β' • W)) (C * N) ((N : ℝ) ^ (-a))}
          ≤ ENNReal.ofReal ((N : ℝ) ^ (-a)) := by sorry

end SKAnnealing.Sampling
