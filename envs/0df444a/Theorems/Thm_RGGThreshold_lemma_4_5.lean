-- Prove2me | Theorems.Thm_RGGThreshold_lemma_4_5
-- name    : RGGThreshold.lemma_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T18:01:22.987616+00:00
-- url     : https://prove2.me/theorems/a66e222b-0b0f-41b1-a4cd-802ad4a848fb
-- title:
--   Lemma 4.5 — $z_p\sim\sqrt{2\log p^{-1}}$ and $c_{p,k}=z_p+\tilde O(1/k)$
-- statement:
--   Let $z_p=\Phi^{-1}(1-p)$ and, for an integer $k\ge3$ and $p\in(0,1/3)$, let $c_{p,k}$ be the real number with $\mathbb P[Y\ge c_{p,k}]=p$ for $Y\sim S_k$ (the law of $\sqrt k\,y(1)$, $y$ uniform on $\mathbb S^{k-1}$). Then:
--
--   1. $z_p=(1+o(1))\sqrt{2\log p^{-1}}$ as $p\to0$, that is
--
--   $$
--   \lim_{p\to0^+}\frac{z_p}{\sqrt{2\log(1/p)}}=1 ;
--   $$
--
--   2. there are constants $C,B$ such that for every $k\ge3$ and every $p$ with $1/k\le p<1/3$,
--
--   $$
--   |c_{p,k}-z_p|\le C\,\frac{(\log k)^B}{k}.
--   $$
--
--   The second clause is how the paper passes between the sphere threshold $c_p=c_{p,d}$ and the Gaussian quantile $z_p$.
--
--   Differences from the source:
--
--   - encoding: c_{p,k} = Ψ_k^{-1}(1−p) → every c with P[√k·y(1) ≥ c] = p; reason: c_{p,k} is the unique such number for k ≥ 2; the Lean statement holds for every solution
--   - reading: c_{p,k} = z_p + Õ(1/k) for p ≥ 1/k → |c − z_p| ≤ C(log k)^B/k with C, B chosen before k, p, c; reason: Õ allows constant-power logarithms (§4.1); on this range log(1/p) ≤ log k
--   - reading: z_p = (1 + o(1))√(2 log p⁻¹) as p → 0 → z_p/√(2 log(1/p)) → 1 as p → 0⁺; reason: the o(1) statement as a limit
-- source:
--   Hunter–Milojević–Sudakov, Distinguishability Threshold for Random Geometric Graphs, arXiv:2607.22480 (held version, sha256 1a398ef9…), Lemma 4.5, p.13 (PDF p.15)

import Mathlib
import Definitions.Def_RGGThreshold_gaussCDF
import Definitions.Def_RGGThreshold_sphCDF

namespace RGGThreshold

/-- **Lemma 4.5** (Hunter–Milojević–Sudakov, arXiv:2607.22480, held version, sha256 1a398ef9…,
Lemma 4.5, p.13 (PDF p.15)). We have `z_p = (1 + o(1)) √(2 log p⁻¹)` as `p → 0`, and, for an integer
`k ≥ 3` and `p ∈ (0, 1/3)` with `p ≥ 1/k`, `c_{p,k} = z_p + Õ(1/k)`, where `c_{p,k}` is the real number
with `P[Y ≥ c_{p,k}] = p` for `Y ∼ S_k`, the law of `√k · y(1)` with `y` uniform on `S^{k-1}`.

**Formalization Note** The first clause is a limit along `p → 0⁺`. In the second, `c_{p,k}` is
any `c` with `P[√k · y(1) ≥ c] = p`, and `Õ(1/k)` is `C (log k)^B / k` with `C, B` chosen before `k`,
`p` and `c`; `log p⁻¹ ≤ log k` on this range. -/
theorem lemma_4_5 :
    Filter.Tendsto (fun p : ℝ => zp p / Real.sqrt (2 * Real.log (1 / p)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) ∧
    ∃ (C : ℝ) (B : ℕ), ∀ k : ℕ, 3 ≤ k → ∀ p : ℝ, 1 / (k : ℝ) ≤ p → p < 1 / 3 → ∀ c : ℝ,
      (RGGDetect.unifSphere k).real {y | c ≤ Real.sqrt k * firstCoord y} = p →
      |c - zp p| ≤ C * Real.log k ^ B / k := by sorry

end RGGThreshold
