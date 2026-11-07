-- Prove2me | Theorems.Thm_SingleOrSample_lemma_4_5
-- name    : SingleOrSample.lemma_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:49:56.463012+00:00
-- url     : https://prove2.me/theorems/5d756521-f1a5-45b1-a604-350e725fca46
-- title:
--   Lemma 4.5 — single-agent failure probability
-- statement:
--   Let $k>0$, $\tau>0$, $\gamma=1-(2k+1)\tau$, and let $\lambda>0$ satisfy
--   $$\psi(\lambda)=\frac{e^\lambda-1}{k}\le\lambda\gamma.$$
--   Let agent $i$ have a monotone, normalized, submodular valuation $v$ with $\mathrm{MMS}_v=1$ and follow the safe strategy at target $\tau$, and let all strategies be legal. Then
--   $$\Pr[v(A_i)<\tau]\le\exp\bigl(-\lambda\gamma(n-i+1)\bigr).$$
--   The bound is smallest for the first agent and weakest for the last. Summing it over the agents gives the failure budget of the main theorem.
--
--   **Formalization Note** Lean's agent index starts at $0$, so the exponent in Lean is $n-i$ for Lean's $i$, which is the page's $n-i+1$ for the page's $i$.
--
--   Differences from the source:
--   - encoding: agent i ∈ [n], exponent n − i + 1 → i : Fin n from 0, exponent n − i; reason: index shift, the same number
--   - encoding: τ = 1/ck → 0 < k and any τ > 0; reason: the same as a positive real c; k = 0 leaves ψ undefined
--   - encoding: the agent's failure event → the law of the whole run of n rounds; reason: the agent's bundle does not depend on later rounds
-- source:
--   Chawla, Huang, Kulkarni, Mehta, Shahkar, Single-or-Sample: Online Fair Allocation for Combinatorial Agents, STOC 2027 submission, arXiv:2609.32286 (manuscript sha256 28cd3d7b…), Lemma 4.5, eq. (8), p.17

import Mathlib
import Definitions.Def_LittleCharity_MMS_Setting
import Definitions.Def_SubsamplingSM_Offline_IsSubmodular
import Definitions.Def_SingleOrSample_IsValuation
import Definitions.Def_SingleOrSample_runLaw
import Definitions.Def_SingleOrSample_IsSafe

namespace SingleOrSample

/-- **Lemma 4.5, single-agent failure probability** (Chawla, Huang, Kulkarni, Mehta, Shahkar, Single-or-Sample: Online Fair Allocation for Combinatorial Agents, STOC 2027 submission, arXiv:2609.32286 (manuscript sha256 28cd3d7b…), Lemma 4.5, p.17). Let `γ = 1 − (2k + 1)τ` and
`λ > 0` with `(e^λ − 1)/k ≤ λγ`. An agent with a normalized submodular valuation following the safe strategy,
against any legal profile, fails with `Pr[v(A_i) < τ] ≤ exp(−λγ(n − i + 1))`.

**Formalization Note.** Lean's `i : Fin n` (from `0`) is the page's `i + 1`, so the page's `n − i + 1` is
`n − i` here. `MMS v = 1` is the normalization of §4.2 (Definition 3, p.6). The whole run's law is used; the
agent's bundle does not depend on later rounds. -/
theorem lemma_4_5 {m n k : ℕ} (hk : 0 < k) {τ : ℝ} (hτ : 0 < τ) (v : Finset (Fin m) → ℝ)
    (hv : IsValuation v) (hsub : SubsamplingSM.Offline.IsSubmodular v)
    (hmms : LittleCharity.MMS.mms v n Finset.univ = 1) (σ : Fin n → Strategy m)
    (hσ : ∀ j, Legal n k (σ j)) (i : Fin n) (hsafe : IsSafe n k τ v (σ i)) {lam : ℝ} (hlam : 0 < lam)
    (h7 : (Real.exp lam - 1) / (k : ℝ) ≤ lam * (1 - (2 * (k : ℝ) + 1) * τ)) :
    (runLaw k σ n).toOuterMeasure {h | v (allocOf h i) < τ} ≤
      ENNReal.ofReal
        (Real.exp (-(lam * (1 - (2 * (k : ℝ) + 1) * τ) * ((n : ℝ) - (i : ℕ))))) := by sorry

end SingleOrSample
