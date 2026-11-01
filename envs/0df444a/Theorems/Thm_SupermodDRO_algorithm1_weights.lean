-- Prove2me | Theorems.Thm_SupermodDRO_algorithm1_weights
-- name    : SupermodDRO.algorithm1_weights
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:32:25.681975+00:00
-- url     : https://prove2.me/theorems/ca00deaa-9173-4e6c-94e6-0fbea5e2f9c0
-- title:
--   Proof of Theorem 1, p.48 — the weights of Algorithm 1 lie in $[0,1]$ and sum to $1$ (corrected: Algorithm 1 masses on degenerate coordinates)
-- statement:
--   Fix a scenario whose data satisfy the assumptions of p.7, with $n\ge1$. The weights $p=(p_1,\dots,p_{2n+1})$ returned by Algorithm 1 satisfy
--   $$
--   0\le p_i\le1\quad(i\in[2n+1]),\qquad \sum_{i\in[2n+1]}p_i=1 .
--   $$
--   The paper uses $p_i\in[0,1]$ in the proof of Theorem 1; the sum condition is what makes $\sum_ip_i\,g(x,z^i)$ in Proposition 3 an expectation.
--
--   **Formalization Note** Algorithm 1 uses the masses $(1,0,0)$ on coordinates with $\underline z_i=\overline z_i$; with the printed masses $(1,1,1)$ a one-coordinate run returns the weights $(1,1,1)$.
--
--   Differences from the source:
--   - correction: Algorithm 1 reads the masses 1, 1, 1 of p.8 for a coordinate with z̲ᵢᵏ = z̄ᵢᵏ → masses (1, 0, 0) on the levels lower, mean, upper; reason: with the printed masses the weights sum to 3 and Theorem 1 fails: n = K = 1, δ = 0, g ≡ 1 give value 1 for (2) and 3 for (6), with every assumption of the paper satisfied
--   - generalization: pᵢᵏ ∈ [0, 1] → pᵢ ∈ [0, 1] and Σᵢ pᵢ = 1; reason: a stronger conclusion that contains the source's claim
--   - reading: z̲ᵏ ≤ µᵏ ≤ z̄ᵏ and δᵏ ≥ 0 are never stated → assumed (in ScenarioAssumptions); reason: used throughout the paper: the support contains the mean, (5) is a probability vector, and p.7 treats µᵢᵏ ∈ {z̄ᵢᵏ, z̲ᵢᵏ} as the boundary case
--   - encoding: n unrestricted → 0 < n; reason: Algorithm 1 takes a minimum over [n] and is undefined for n = 0; no instance where it is defined is excluded
--   - encoding: Algorithm 1 tracks the values of the coordinates → Algorithm 1 tracks their levels lower, mean, upper; reason: identical on coordinates with z̲ᵢ < µᵢ < z̄ᵢ; on z̲ᵢ = z̄ᵢ all levels have the same value
--   - encoding: [K], [n], [2n+1] indexed from 1 → Fin K, Fin n, Fin (2n+1) indexed from 0; reason: Lean convention; same instances
-- source:
--   Long, Qi & Zhang, Supermodularity in Two-Stage Distributionally Robust Optimization, author manuscript (June 2022; PDF sha256 9e6840ad…5b09160b02b5e47), Proof of Theorem 1 (App. C.4), p.48

import Mathlib
import Definitions.Def_SupermodDRO_ScenarioAssumptions
import Definitions.Def_SupermodDRO_algorithm1

namespace SupermodDRO

/-- **The weights of Algorithm 1 lie in `[0, 1]` (and sum to `1`).** Long, Qi & Zhang,
*Supermodularity in Two-Stage Distributionally Robust Optimization*, author manuscript (June 2022),
Proof of Theorem 1 (App. C.4), p.48: "Again, since pᵢᵏ ∈ [0, 1] for all i ∈ [2n + 1], there exists a
specific i ∈ [2n + 1] such that g(x, z^{k,i}) = ∞."

For one scenario with data satisfying the assumptions of p.7 and `n ≥ 1`, every weight `pᵢ`
returned by Algorithm 1 lies in `[0, 1]`, and the weights sum to `1`.

**Formalization Note** The sum clause is not on the page; it is what makes Proposition 3's right-hand
side an expectation, and it holds only with the corrected masses `(1, 0, 0)` on coordinates with
`z̲ᵢ = z̄ᵢ` (with the printed masses `(1, 1, 1)` the weights of a one-coordinate run are `(1, 1, 1)`). -/
theorem algorithm1_weights {n : ℕ} (μ δ zl zu : Fin n → ℝ) (hsc : ScenarioAssumptions μ δ zl zu)
    (hn : 0 < n) :
    (∀ i, 0 ≤ algorithm1Weight μ δ zl zu i ∧ algorithm1Weight μ δ zl zu i ≤ 1) ∧
      ∑ i, algorithm1Weight μ δ zl zu i = 1 := by sorry

end SupermodDRO
