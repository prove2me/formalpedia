-- Prove2me | Theorems.Thm_RecoveringBandits_rs_ratio
-- name    : RecoveringBandits.rs_ratio
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:57:42.615989+00:00
-- url     : https://prove2.me/theorems/4e0edcfb-7a5f-4af1-b617-d9ef2ca39812
-- title:
--   §4.3: $K[a]\le K+a$ and every R-S output earns at least $\frac a{a+1}\cdot\frac K{K+a}\cdot\mathrm{UB}_R[K]$ in the long run
-- statement:
--   Let the instance be admissible, $K\ge1$, $a\ge1$, let $x^*$ be an optimal solution of (3) with the property of Lemma 2, and let $x$ be its lift by line 7 of Algorithm 2 ($x_i=0$ if $x^*_i=0$, else the smallest $1/d^{(k)}_i\ge x^*_i$). With $d_i$ the rounding (4) of $x_i$ and $K_j$ as in Step 2,
--
--   1. $\displaystyle K[a]=\sum_{j\in[a]}\lceil K_j\rceil\le K+a$;
--   2. every output $\pi$ of R-S$(x,K,a)$ satisfies
--   $$\frac{a}{a+1}\cdot\frac{K}{K+a}\cdot\mathrm{UB}_R[K]\le\sum_{i:\,d_i(\pi)<+\infty}\frac{R_i(d_i)}{d_i}.$$
--
--   Maximizing over $a$ gives the long-run ratio $\gamma_K$ of Theorem 1.
--
--   Differences from the source:
--   - generalization: the ratio for the tuned a (max over a ∈ Z+) → the bound for every a ≥ 1 and every output of R-S(x, K, a); reason: the maximum over a is attained at some a, which is one case
--   - generalization: K a positive integer with K ≤ N (§2) → any K ≥ 1; reason: the bound does not use K ≤ N; it specializes to 1 ≤ K ≤ N
--   - encoding: the long-run approximation ratio Σ R_i(d_i)/d_i / Σ F_i(x*_i) · K/K[a] → the long-run reward bounded below by a product with UB_R[K]; reason: UB_R[K] can be 0; Σ F_i(x*_i) = UB_R[K] for an optimal x*
-- source:
--   Simchi-Levi–Zheng–Zhu, Offline Planning and Online Learning under Recovering Rewards, arXiv:2106.14813v2, §4.3, p.14

import Mathlib
import Definitions.Def_RecoveringBandits_Admissible
import Definitions.Def_RecoveringBandits_IsAlg2Run

namespace RecoveringBandits

/-- **§4.3, the ratio of an R-S run**, Simchi-Levi–Zheng–Zhu, arXiv:2106.14813v2, §4.3, p.14
(PDF p.14): let `x*` be an optimal solution of (3) with the property of Lemma 2, `x` its lift by
line 7 of Algorithm 2, and `a ≥ 1`. Then the number of groups satisfies
`K[a] = ∑_{j ∈ [a]} ⌈K_j⌉ ≤ K + a` ("the upper bound of `K[a]` increases from `K + a − 1` to
`K + a`"), and every output `π` of R-S(x, K, a) has long-run average reward
`∑_{i : d_i < +∞} R_i(d_i)/d_i ≥ a/(a+1) · K/(K+a) · UB_R[K]`.

**Formalization Note.** Stated for every `a ≥ 1` (the paper then maximizes over `a`, which gives
`γ_K`); the ratio is multiplied out (`UB_R[K]` can be `0`). -/
theorem rs_ratio {N : ℕ} (R : Fin N → ℕ → ℝ) (Rmax : ℝ) (hR : Admissible R Rmax) (K : ℕ)
    (hK : 1 ≤ K) (a : ℕ) (ha : 1 ≤ a) (xstar : Fin N → ℝ) (hopt : IsOpt3 R K xstar)
    (hL2 : Lemma2Prop R xstar) :
    (∑ j ∈ Finset.Icc 1 a, ⌈Kj a (fun i => lift (R i) (xstar i)) j⌉₊ ≤ K + a) ∧
    ∀ π : PPP N, IsRSRun R K a (fun i => lift (R i) (xstar i)) π →
      ((a : ℝ) / ((a : ℝ) + 1)) * ((K : ℝ) / ((K : ℝ) + a)) * UB R K ≤ longRunReward R π := by sorry

end RecoveringBandits
