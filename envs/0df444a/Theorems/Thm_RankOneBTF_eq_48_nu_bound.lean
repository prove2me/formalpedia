-- Prove2me | Theorems.Thm_RankOneBTF_eq_48_nu_bound
-- name    : RankOneBTF.eq_48_nu_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:25:10.563167+00:00
-- url     : https://prove2.me/theorems/8f6fb569-5bb4-43d6-a4a0-8cf7b89cd525
-- title:
--   Bound (48) — $\mathbb E[\nu^{y,j}_{ik}]\le\frac p3\bigl(\frac1{r_{\bar x}r_{\bar z}}+\frac1{2r_{\bar x}}+\frac1{2r_{\bar z}}+1\bigr)$
-- statement:
--   Consider the fully-random corruption model with parameter $p\in[0,1]$, and let $\bar x$, $\bar z$ have exact ratios of ones $r_{\bar x},r_{\bar z}>0$ ($n_{\bar x}=nr_{\bar x}$, $n_{\bar z}=lr_{\bar z}$). For every $i\in[n]$ with $\bar x_i=1$ and every $(j,k)\in[m]\times[l]$, the random variable $\nu^{y,j}_{ik}$ of (42) satisfies
--   $$
--   \mathbb E\bigl[\nu^{y,j}_{ik}\bigr]\le\frac p3\Bigl(\frac1{r_{\bar x}r_{\bar z}}+\frac1{2r_{\bar x}}+\frac1{2r_{\bar z}}+1\Bigr).\qquad(48)
--   $$
--
--   The bound is used for the expectation in Claim 3 and, "by proof of Claim 3", in Step 2 of Claim 7.
--
--   **Formalization Note** The expectation is the finite weighted sum over corruption patterns (`frExpect`). The bound is for every finite $n,m,l$.
--
--   Differences from the source:
--   - generalization: the setting of Claim 3: 0 < p below the threshold (19) → every p ∈ [0,1]; reason: the computation (46)–(47) is valid for 0 < p < 1, and at p ∈ {0, 1} the variable ν^{y,j}_{ik} vanishes almost surely; the printed range is a special case
--   - encoding: ν^{y,j}_{ik} as a ratio of sums of indicators (42) → phiY / T^{y,j}_{11} on the case condition, 0 otherwise; reason: summing the indicators gives these counts; same random variable
-- source:
--   Del Pia, Khajavirad, Rank-one Boolean tensor factorization and the multilinear polytope, arXiv:2202.07053v3, p.22, (48) (with (42), p.22), proof of Claim 3; reused in Step 2 of Claim 7, p.37

import Mathlib
import Definitions.Def_RankOneBTF_nuY
import Definitions.Def_RankOneBTF_frProb

namespace RankOneBTF

/-- **Bound (48)** (arXiv:2202.07053v3, p.22, proof of Claim 3): in the fully-random
corruption model, for each `i ∈ [n]` with `x̄_i = 1` and each `(j,k)`,
`E[ν^{y,j}_{ik}] ≤ (p/3)(1/(r_x̄ r_z̄) + 1/(2r_x̄) + 1/(2r_z̄) + 1)`, with `ν^{y,j}_{ik}` of (42).
It is reused in Step 2 of Claim 7 (p.37).

**Formalization Note** `r_x̄, r_z̄ > 0` are the exact ratios of ones of `x̄, z̄`
(`n_x̄ = n r_x̄`, `n_z̄ = l r_z̄`, p.20). The expectation is over the fully-random model with
parameter `p ∈ [0,1]` (`frExpect`). The bound is stated for every finite `n, m, l`. -/
theorem eq_48_nu_bound {n m l : ℕ} (p rx rz : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (xb : Fin n → Bool) (yb : Fin m → Bool) (zb : Fin l → Bool)
    (hrx : 0 < rx) (hrz : 0 < rz) (hx : numOnes xb = rx * (n : ℝ))
    (hz : numOnes zb = rz * (l : ℝ)) (i : Fin n) (hi : xb i = true) (j : Fin m) (k : Fin l) :
    frExpect p (groundTruth xb yb zb) (fun G => nuY xb yb zb G i j k) ≤
      p / 3 * (1 / (rx * rz) + 1 / (2 * rx) + 1 / (2 * rz) + 1) := by sorry

end RankOneBTF
