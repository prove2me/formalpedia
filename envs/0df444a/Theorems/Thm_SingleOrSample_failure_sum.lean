-- Prove2me | Theorems.Thm_SingleOrSample_failure_sum
-- name    : SingleOrSample.failure_sum
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:50:29.54613+00:00
-- url     : https://prove2.me/theorems/2bdff52b-6528-426e-b9e3-6ba98e7e089a
-- title:
--   §4.3 — failure sum and constants
-- statement:
--   Three facts make up the bookkeeping of the main theorem.
--
--   1. For $k>0$, $\tau>0$, $\lambda>0$ with $\gamma=1-(2k+1)\tau>0$ and $(e^\lambda-1)/k\le\lambda\gamma$, and normalized submodular agents all following safe strategies:
--   $$\Pr[\text{some agent fails}]\le\sum_{i=1}^ne^{-\lambda\gamma(n-i+1)}<\frac1{e^{\lambda\gamma}-1}.$$
--   2. The choice $k=4$, $c=6$, $\tau=1/(ck)=1/24$, $\gamma=1-9\tau=5/8$, $\lambda=\ln5$ satisfies the constraints: $\gamma>0$ and $(e^{\ln 5}-1)/4=1\le\frac58\ln5$.
--   3. For this choice, for all $n$,
--   $$\sum_{i=1}^ne^{-\lambda\gamma(n-i+1)}<\frac1{5^{5/8}-1}<0.577.$$
--
--   **Formalization Note** Lean's agent index starts at $0$, so the page's $n-i+1$ is $n-i$ in Lean.
--
--   Differences from the source:
--   - encoding: agent i ∈ [n], exponent n − i + 1 → i : Fin n from 0, exponent n − i; reason: index shift, the same number
--   - encoding: c, k, λ with τ = 1/ck → k, τ > 0, λ > 0; reason: the same as a positive real c
-- source:
--   Chawla, Huang, Kulkarni, Mehta, Shahkar, Single-or-Sample: Online Fair Allocation for Combinatorial Agents, STOC 2027 submission, arXiv:2609.32286 (manuscript sha256 28cd3d7b…), §4.3, p.17

import Mathlib
import Definitions.Def_LittleCharity_MMS_Setting
import Definitions.Def_SubsamplingSM_Offline_IsSubmodular
import Definitions.Def_SingleOrSample_IsValuation
import Definitions.Def_SingleOrSample_runLaw
import Definitions.Def_SingleOrSample_IsSafe

namespace SingleOrSample

/-- **Failure sum and constants** (Chawla, Huang, Kulkarni, Mehta, Shahkar, Single-or-Sample: Online Fair Allocation for Combinatorial Agents, STOC 2027 submission, arXiv:2609.32286 (manuscript sha256 28cd3d7b…), §4.3, p.17). Three clauses:
1. for `k`, `τ`, `λ` with `γ = 1 − (2k + 1)τ > 0` and (7), and normalized submodular agents all following
   safe strategies against each other, `Pr[some agent fails] ≤ ∑_i e^{−λγ(n−i+1)} < 1/(e^{λγ} − 1)`;
2. `k = 4`, `c = 6`, `τ = 1/ck = 1/24`, `γ = 1 − 9τ = 5/8`, `λ = ln 5` satisfy these constraints;
3. with these constants `∑_i e^{−λγ(n−i+1)} < 1/(5^{5/8} − 1) < 0.577`.

**Formalization Note.** Lean's `i : Fin n` (from `0`) is the page's `i + 1`, so the page's `n − i + 1` is
`n − i` here. In the first clause only the agents' legality and safety are used, so all profiles of that
form are covered; `1/(e^{λγ} − 1)` is positive since `λγ > 0`. -/
theorem failure_sum :
    (∀ (n m k : ℕ), 0 < k → ∀ τ : ℝ, 0 < τ → ∀ lam : ℝ, 0 < lam →
      0 < 1 - (2 * (k : ℝ) + 1) * τ →
      (Real.exp lam - 1) / (k : ℝ) ≤ lam * (1 - (2 * (k : ℝ) + 1) * τ) →
      ∀ vs : Fin n → Finset (Fin m) → ℝ,
        (∀ i, IsValuation (vs i) ∧ SubsamplingSM.Offline.IsSubmodular (vs i) ∧
          LittleCharity.MMS.mms (vs i) n Finset.univ = 1) →
        ∀ σ : Fin n → Strategy m, (∀ j, Legal n k (σ j)) → (∀ i, IsSafe n k τ (vs i) (σ i)) →
          (runLaw k σ n).toOuterMeasure {h | ∃ i : Fin n, vs i (allocOf h i) < τ} ≤
            ENNReal.ofReal (∑ i : Fin n,
              Real.exp (-(lam * (1 - (2 * (k : ℝ) + 1) * τ) * ((n : ℝ) - (i : ℕ))))) ∧
          ∑ i : Fin n, Real.exp (-(lam * (1 - (2 * (k : ℝ) + 1) * τ) * ((n : ℝ) - (i : ℕ)))) <
            1 / (Real.exp (lam * (1 - (2 * (k : ℝ) + 1) * τ)) - 1)) ∧
    ((1 : ℝ) / (6 * 4) = 1 / 24 ∧ 1 - (2 * (4 : ℝ) + 1) * (1 / 24) = 5 / 8 ∧
      (0 : ℝ) < 5 / 8 ∧ (Real.exp (Real.log 5) - 1) / 4 ≤ Real.log 5 * (5 / 8)) ∧
    (∀ n : ℕ, ∑ i : Fin n, Real.exp (-(Real.log 5 * (5 / 8) * ((n : ℝ) - (i : ℕ)))) <
        1 / ((5 : ℝ) ^ ((5 : ℝ) / 8) - 1)) ∧
    1 / ((5 : ℝ) ^ ((5 : ℝ) / 8) - 1) < 0.577 := by sorry

end SingleOrSample
