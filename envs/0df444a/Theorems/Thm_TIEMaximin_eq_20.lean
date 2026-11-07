-- Prove2me | Theorems.Thm_TIEMaximin_eq_20
-- name    : TIEMaximin.eq_20
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:44:20.997874+00:00
-- url     : https://prove2.me/theorems/69661495-f870-42de-9381-97ae78b74253
-- title:
--   Equation (20) — Case 1: $P=\{g:f_g>(n-1)/2\}$ is an eligible prefix of small cost
-- statement:
--   Let $m\ge n\ge2$, $\alpha=1/6$, $v$ a nonnegative profile, and suppose every agent only retains her nominated goods: $h_{jg}=0$ whenever $g\notin T_j$. Let $P=\{g:f_g>(n-1)/2\}$. Then $P$ is one of the prefixes $P_t$. For every deficient agent $i$, $P$ is eligible for $i$ and
--
--   $$|P\setminus H_i|+\lceil\rho(P)\rceil\le6a_i-2k_i+1.$$
--
--   This is Case 1 of the proof of (19).
--
--   Differences from the source:
--   - encoding: P is one of the prefixes; P is eligible → ∃ t ≤ m with `prefixP v t` equal to P, eligibility stated at that t; reason: a prefix is identified by its index
--   - encoding: agents N, goods M, nonnegative additive valuations → `Fin n`, `Fin m` (0-based), real matrices with the hypothesis `Nonneg`, bundle value `valOf`; reason: Lean convention; same instances
-- source:
--   M. Ma, B. Tao, F. Wang, Truthful-in-Expectation Mechanism with Constant Maximin-Share Guarantee, arXiv:2609.35670 (version of 2026-11-03, sha256 4e68de70…), §5.2.1, eq. (20), p.24

import Mathlib
import Definitions.Def_TIEMaximin_Basic
import Definitions.Def_TIEMaximin_Comparison

namespace TIEMaximin

open Finset

/-- **Equation (20)** (§5.2.1, p.24). In Case 1 (every agent only retains her nominated goods), let `P
= {g : f_g > (n−1)/2}`. Then `P` is one of the prefixes `P_t`, `P` is eligible for every deficient
agent `i`, and `|P ∖ H_i| + ⌈ρ(P)⌉ ≤ 6a_i − 2k_i + 1`.

arXiv:2609.35670, version of 2026-11-03, sha256 4e68de70…, §5.2.1, eq. (20), p.24.

**Formalization Note.** `α = 1/6`. The case hypothesis is `∀ j g, g ∉ T_j → h_jg = 0` (p.24). "P
is eligible" is stated for the `t` with `P_t = P`. -/
theorem eq_20 {n m : ℕ} (hn : 2 ≤ n) (hnm : n ≤ m) (v : Fin n → Fin m → ℝ) (hv : Nonneg v)
    (hcase : ∀ j g, g ∉ topSet v j → hRet (1 / 6) v j g = 0)
    (i : Fin n) (hi : IsDeficient (1 / 6) v i) :
    ∃ t, t ≤ m ∧
      prefixP v t = Finset.univ.filter (fun g => ((n : ℝ) - 1) / 2 < (nom v g : ℝ)) ∧
      IsEligible (1 / 6) v i t ∧
      ((#(prefixP v t \ high (1 / 6) v i) : ℕ) : ℤ) + ⌈rho (1 / 6) v (prefixP v t)⌉ ≤
        6 * aDef (1 / 6) v i - 2 * (kDef (1 / 6) v i : ℤ) + 1 := by sorry

end TIEMaximin
