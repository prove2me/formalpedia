-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P58_d3_large_tip_expansion
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P58.d3_large_tip_expansion
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T09:57:06.349774+00:00
-- url     : https://prove2.me/theorems/322101a5-028c-4912-b5a8-bc2017e4b0ba
-- title:
--   Large-tip D3 cylinder profile
-- statement:
--   There exist a family $r_t(z)$ of regular dimensionless D3 cylinder profiles, with $t>0$, $r_t(1)=t$, and boundary radius $r_t(0)$, and a function $f\in C^1([0,1])$ with $f(1)=0$, such that for every fixed $0<a<1$,
--
--   $$
--   r_t(z)=t+\frac{f(z)}t+o(t^{-1})\qquad(t\to\infty)
--   $$
--
--   uniformly for $z\in[a,1]$. Equivalently, for every $\epsilon>0$ there is $T>0$, independent of $t$ and $z$, for which $|t(r_t(z)-t)-f(z)|\le\epsilon$ whenever $t\ge T$ and $a\le z\le1$.
--
--   Every member solves the source Euler–Lagrange equation and has finite positive-cutoff area; the asymptotic expansion is derived as a conclusion. This describes approach to a straight cylinder on regulated intervals. It does not identify the entropy-minimizing branch.
--
--   The boundary value is included separately: $t(r_t(0)-t)\to f(0)$ as $t\to\infty$, so $R_t=r_t(0)=t+f(0)/t+o(t^{-1})$. This is the boundary-radius consequence used in passing from (3.22) to (3.24).
-- source:
--   Topological Entanglement Entropy and Holography, arXiv:0805.1891v2, PDF p. 11, (3.22)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P58

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P58

open Set Filter MeasureTheory

open scoped Topology

/-- PDF p.11, (3.22): construct the regular D3 cylinder family and its large-tip
correction, including R=r(0)=r0+f(0)/r0+o(1/r0) at the boundary.
The o(1/r0) estimate is uniform on each fixed compact regulated z interval. The reference to solving (3.21) means the ODE (3.20) with that
endpoint data. No large-radius expansion is assumed as a premise. -/
theorem d3_large_tip_expansion :
    ∃ (C : ℝ → ℝ → ℝ) (f : ℝ → ℝ),
      (∀ t : ℝ, 0 < t → IsCylinder .d3 (C t 0) (C t) ∧ C t 1 = t) ∧
      f 1 = 0 ∧ (∀ z ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ 1 f z) ∧
      Tendsto (fun t => t * (C t 0 - t)) atTop (nhds (f 0)) ∧
      ∀ a : ℝ, 0 < a → a < 1 → ∀ epsilon : ℝ, 0 < epsilon →
        ∃ T : ℝ, 0 < T ∧ ∀ t : ℝ, T ≤ t →
          ∀ z ∈ Icc a 1, |t * (C t z - t) - f z| ≤ epsilon := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P58

end
