-- Prove2me | Theorems.Thm_PermLimits_Existence_density_stepLimit_close
-- name    : PermLimits.Existence.density_stepLimit_close
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T14:00:18.988983+00:00
-- url     : https://prove2.me/theorems/67fedd4d-603b-4ed8-b712-07b2b06b35d3
-- title:
--   Lemma 3.5: $|t(\tau,\sigma)-t(\tau,Z_\sigma)|\le\frac1n\binom k2$
-- statement:
--   Let $\tau\in S_k$ and $\sigma\in S_n$ with $k\le n$. Then
--   $$|t(\tau,\sigma)-t(\tau,Z_\sigma)|\le\frac1n\binom k2 . \tag{27}$$
--
--   Densities of a permutation and of its step limit permutation $Z_\sigma$ agree up to $O(k^2/n)$, so for sequences with $|\sigma_n|\to\infty$ the two families of densities have the same limits. This is what lets the whole theory be run on $\mathcal Z$.
--
--   **Formalization Note** $k\ge1$ is assumed, as in the source ($\tau\in S_k$ for a positive integer $k$); with $k\le n$ it gives $n\ge1$. The source's permutation is named $\sigma$; the Lean statement calls it $\pi$ because $\sigma$ is reserved notation.
-- source:
--   Hoppen, Kohayakawa, Moreira, Ráth, Sampaio, Limits of permutation sequences, arXiv:1103.5844v2, https://arxiv.org/abs/1103.5844v2, p. 11, Lemma 3.5 (Eq. (27))

import Mathlib
import Definitions.Def_PermLimits_Shared_PermDensity
import Definitions.Def_PermLimits_Shared_LimitMeasure
import Definitions.Def_PermLimits_Shared_StepLimit
open PermLimits.Shared

namespace PermLimits.Existence

open unitInterval

/-- **Lemma 3.5** (Hoppen et al., *Limits of permutation sequences*, arXiv:1103.5844v2, p. 11).
Let `τ ∈ S_k`, `π ∈ S_n`, `k ≤ n`. Then `|t(τ, π) − t(τ, Z_π)| ≤ (1/n) · C(k, 2)` (Eq. (27)).

**Formalization Note.** The paper's permutation is called `σ`; here `π` (`σ` is reserved notation
once `unitInterval` is opened). `k ≥ 1` is the paper's standing convention that `τ ∈ S_k` for a
positive integer `k` (Definition 1.1); with `k ≤ n` it gives `n ≥ 1`, so `1/n` is a genuine
quotient. -/
theorem density_stepLimit_close {k n : ℕ} (τ : Equiv.Perm (Fin k)) (π : Equiv.Perm (Fin n))
    (hk : 0 < k) (hkn : k ≤ n) :
    |permDensity τ π - limitDensity τ (stepLimit π)| ≤ (1 / (n : ℝ)) * (Nat.choose k 2 : ℝ) := by sorry

end PermLimits.Existence
