-- Prove2me | Theorems.Thm_SKAnnealing_Sampling_lemma_5_1
-- name    : SKAnnealing.Sampling.lemma_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:16:35.9149+00:00
-- url     : https://prove2.me/theorems/821fcd57-9718-40f5-b45e-67a9f081499a
-- title:
--   Lemma 5.1, p. 21 — the TAP Hessian satisfies $K_t\succeq\gamma_{\beta,T}$ for $t\in[0,T]$ with probability $1-N^{-a}$
-- statement:
--   Throughout, $0<\beta<1$, $W\sim\mathrm{GOE}(N)$, $x\sim\mathrm{Unif}\{\pm1\}^N$ and $g\sim\mathcal N(0,\mathrm{Id})$ are independent, $\mu_t$ is the measure of Theorem 1.4, $\mathbf{Cov}=\mathbf{Cov}(\mu_t)$, and $K$, $m$, $v_i$, $q_N$, $d_i$, $\lambda_i$, $f_i$ are the TAP quantities (8) at $\mu_t$, with $M=W+\frac\beta Nxx^\top$ (diagonal zeroed). $K_t$ is $K$ at the measure $\mu_t$.
--
--   **Lemma 5.1.** For every $T>0$ there is a constant $\gamma=\gamma_{\beta,T}>0$ such that for every constant $a>0$ there is $N_0$ with, for all $N\ge N_0$ and all $t\in[0,T]$,
--   $$\Pr\big[K_t\not\succeq\gamma\,\mathrm{Id}\big]\le N^{-a}.$$
--
--   This is the precise form of Lemma 4.2 (smallest eigenvalue of the TAP Hessian). Since $\gamma$ is chosen before $a$, the lower bound holds with polynomially small failure probability of every order.
--
--   Differences from the source:
--   - reading: Let T > 0 large; a constant γ = γ_{β,T} → every T > 0, and γ > 0; reason: the claim for a larger T implies it for a smaller one ([0, T] ⊂ [0, T′]), so "for all large T" is "for all T > 0"; γ > 0 is printed in Lemma 4.2, of which Lemma 5.1 is the precise version
--   - encoding: for any constant a → for every a > 0; reason: for a ≤ 0 and N ≥ 1 the bound N^{−a} ≥ 1 holds trivially
--   - reading: t ∈ [0, T] → one N₀ for every t ∈ [0, T]; reason: uniformity over the bounded time range, as in reading R5
--   - encoding: Pr[…] ⩽ N^{−a} → for every N ≥ N₀, the measure of the failure event is ≤ N^{−a} (constant 1 kept); reason: the bound is asymptotic in N; the constant 1 of the page is kept (reading R4)
--   - encoding: W ∼ GOE(N), a symmetric matrix with diagonal entries → the off-diagonal entries W_{ik}, i < k, iid N(0, 1/N) (OAI.CriticalSK.disorderLaw); no diagonal; reason: σ_i² = 1, so the diagonal only adds a constant to the Hamiltonian and changes no Gibbs measure, kernel or covariance (reading R8)
-- source:
--   Du, Huang, Mohanty, Rajaraman, Sampling from the Sherrington–Kirkpatrick Model up to Criticality, arXiv:2610.17717 (PDF of October 29, 2026), Lemma 5.1, display (15), p. 21 (PDF p. 23); Lemma 4.2, p. 16

import Mathlib
import Definitions.Def_CriticalSK
import Definitions.Def_SKAnnealing_Sampling_lawMean
import Definitions.Def_SKAnnealing_Sampling_tilt
import Definitions.Def_SKAnnealing_Sampling_plantedTilted
import Definitions.Def_SKAnnealing_Sampling_tapHessian

open OAI.CriticalSK MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace SKAnnealing.Sampling

/-- **Lemma 5.1** (more precise version of Lemma 4.2). Let `T > 0` large. There exists a constant
`γ = γ_{β,T}` such that for any constant `a` and `t ∈ [0, T]`, `Pr[K_t ⋡ γ] ≤ N^{−a}`.

Du, Huang, Mohanty, Rajaraman, *Sampling from the Sherrington–Kirkpatrick Model up to Criticality*, arXiv:2610.17717 (PDF of October 29, 2026), Lemma 5.1, display (15), p. 21 (PDF p. 23); Lemma 4.2, p. 16 (`γ > 0`).

**Formalization Note** `γ > 0` as in Lemma 4.2, chosen before `a`. "`T > 0` large" is stated for every `T > 0`
(the claim for a larger `T` implies it for a smaller one). `K_t ⪰ γ` is `(K_t − γ Id).PosSemidef`. Standing
setting of Section 4, uniformly over `t ∈ [0, T]` (including `t = 0`) for `N ≥ N₀` (R4, R5). -/
theorem lemma_5_1 :
    ∀ β : ℝ, 0 < β → β < 1 → ∀ T : ℝ, 0 < T → ∃ γ : ℝ, 0 < γ ∧ ∀ a : ℝ, 0 < a →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ t : ℝ, 0 ≤ t → t ≤ T →
        plantedFieldLaw N {ω |
            ¬ (tapHessian β (plantedMatrix β ω.1.1 ω.1.2) (plantedTilted β t ω.1.1 ω.1.2 ω.2)
                - γ • (1 : Matrix (Fin N) (Fin N) ℝ)).PosSemidef}
          ≤ ENNReal.ofReal ((N : ℝ) ^ (-a)) := by sorry

end SKAnnealing.Sampling
