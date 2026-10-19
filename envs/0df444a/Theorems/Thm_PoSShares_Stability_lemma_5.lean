-- Prove2me | Theorems.Thm_PoSShares_Stability_lemma_5
-- name    : PoSShares.Stability.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:31:24.783791+00:00
-- url     : https://prove2.me/theorems/06a2e762-b8f7-434d-ace4-d2a22ab05a75
-- title:
--   Lemma 5, (A23) — for $R_t = \rho N_{t-1}^\gamma$, $\gamma<1$: $a_{t+1} \le \frac{\rho}{1-\gamma}N^{\gamma-1}$
-- statement:
--   Let $\rho > 0$, $\gamma \in [0, 1)$ and $N > 0$. For all $t \ge 1$ let $R_t = \rho N_{t-1}^{\gamma}$ and $N_t = N + \sum_{n=1}^t R_n$ (with $N_0 = N$), and let $a_t$ be the sequence (A12). Then for all $t \ge 1$,
--   $$a_{t+1} \le \frac{\rho}{1-\gamma}\,N^{\gamma-1}.$$
--
--   Since $\gamma < 1$, the bound tends to $0$ as the initial supply $N \to \infty$, uniformly in $t$.
--
--   **Formalization Note.** The hypothesis $N > 0$ is added; the page omits it (Lemma 4 states it), and $N^{\gamma-1}$ needs it. Powers are real powers.
-- source:
--   Roşu, Saleh, Evolution of Shares in a Proof-of-Stake Cryptocurrency, author's manuscript of July 30, 2020 (sha256 90d9c06b…2b35eb), p. 22, Lemma 5, (A23)

import Mathlib
import Definitions.Def_PoSShares_Stability_Model
import Definitions.Def_PoSShares_Stability_VarianceSeq

open MeasureTheory ProbabilityTheory Filter Topology

namespace PoSShares.Stability

/-- **Lemma 5, (A23)**, p. 22. Roşu, Saleh, *Evolution of Shares in a Proof-of-Stake Cryptocurrency*, author's manuscript of
July 30, 2020 (sha256 90d9c06b…2b35eb).

Let `ρ > 0` and `γ ∈ [0, 1)`. For all `t ∈ ℕ₊` let `R_t = ρ N_{t−1}^γ` and
`N_t = N + Σ_{n=1}^t R_n`, and let `a_t` be the sequence (A12). Then for all `t ∈ ℕ₊`,
`a_{t+1} ≤ ρ/(1 − γ) · N^{γ−1}`.

**Formalization Note.** `0 < N` is added: the page omits it, but Lemma 4 has it and `N^{γ−1}`
and the integral from `N` in the proof need it. Powers are real powers (`Real.rpow`). -/
theorem lemma_5 (ρ γ N : ℝ) (R : ℕ → ℝ) (hρ : 0 < ρ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1) (hN : 0 < N)
    (hR : IsPowerReward ρ γ N R) :
    ∀ t : ℕ, 1 ≤ t → aSeq N R (t + 1) ≤ ρ / (1 - γ) * N ^ (γ - 1) := by sorry

end PoSShares.Stability
