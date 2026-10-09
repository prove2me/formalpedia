-- Prove2me | Theorems.Thm_SBMThreshold_Main_theorem_2_8_1
-- name    : SBMThreshold.Main.theorem_2_8_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:18:10.122638+00:00
-- url     : https://prove2.me/theorems/e5389c4f-0569-4d45-ae84-4bfbee596d30
-- title:
--   Theorem 2.8 (1), p. 5 — E[Y_{u,v} | σ_U] = (1 + n^{−1+o(1)}) σ_uσ_v s^k/n
-- statement:
--   Assume Assumption 2.7 for $a_n,b_n,\ell_n$, let $s_n^2/d_n\ge\lambda>1$ for all $n$, let $\alpha>0$ satisfy $n^2d_n^{\alpha\log n}\le s_n^{2\alpha\log n}$ for every $n$, and put $k=\lceil\alpha\log n\rceil$. Let $Y_{u,v}$ be the sum of $X_\gamma$ over the self-avoiding paths of length $k$ from $u$ to $v$.
--
--   For every sequence $e_n\to0$ there is a sequence $c_n\to0$ such that, for all $n$, all distinct vertices $u,v$, all vertex sets $U\ni u,v$ with $|U|\le n^{e_n}$ and all labellings $\tau$,
--   $$
--   \Bigl|\mathbb E[Y_{u,v}\mid\sigma_U=\tau_U]-\frac{\tau_u\tau_v\,s^k}{n}\Bigr|\le n^{-1+c_n}\,\frac{|s|^k}{n}.
--   $$
--   That is, $\mathbb E[Y_{u,v}\mid\sigma_U]=(1+n^{-1+o(1)})\sigma_u\sigma_vs^k/n$ uniformly.
--
--   This is the first-moment half of the paper's main technical result: the self-avoiding path sum $Y_{u,v}$ is correlated with $\sigma_u\sigma_v$.
--
--   **Formalization Note** "$U$ of cardinality at most $n^{o(1)}$" is an asymptotic statement in the antecedent and is read by the convention of §1.3: for every $e_n\to0$; the error sequence $c_n$ may depend on $e_n$ and on the parameters, but not on the vertices, the sets or the labellings. The theorem lists four distinct vertices $u,v,u',v'$; display (1) concerns only $u\ne v$.
-- source:
--   Mossel, Neeman and Sly, A Proof of the Block Model Threshold Conjecture, arXiv:1311.4115v4, p. 5, Theorem 2.8, display (1) (with Assumption 2.7, p. 5)

import Mathlib
import Definitions.Def_SBMThreshold_Main_Setting
import Definitions.Def_SBMThreshold_Main_Paths
open Filter Topology Finset

namespace SBMThreshold.Main

/-- Theorem 2.8 (1) (p. 5): under Assumption 2.7 and the preamble of Theorem 2.8, uniformly over
distinct `u, v`, sets `U ⊇ {u, v}` of size at most `n^{o(1)}` and labellings of `U`,
`E[Y_{u,v} | σ_U] = (1 + n^{-1+o(1)}) σ_u σ_v s^k / n` with `k = ⌈α log n⌉`. -/
theorem theorem_2_8_1 (a b : ℕ → ℝ) (ℓ : ℕ → ℕ) (lam α : ℝ)
    (hA : Assumption27 a b ℓ) (hP : Theorem28Params a b lam α) :
    ∀ e : ℕ → ℝ, Tendsto e atTop (𝓝 0) →
      ∃ c : ℕ → ℝ, Tendsto c atTop (𝓝 0) ∧
        ∀ (n : ℕ) (u v : Fin n) (U : Finset (Fin n)) (τ : Fin n → Bool),
          u ≠ v → u ∈ U → v ∈ U → (U.card : ℝ) ≤ (n : ℝ) ^ (e n) →
          |condExp n (a n) (b n) U τ (fun _ G => pathY n (a n) (b n) (pathLen α n) u v G) -
              spin (τ u) * spin (τ v) * sPar (a n) (b n) ^ pathLen α n / n| ≤
            (n : ℝ) ^ (-1 + c n) * (|sPar (a n) (b n)| ^ pathLen α n / n) := by sorry

end SBMThreshold.Main
