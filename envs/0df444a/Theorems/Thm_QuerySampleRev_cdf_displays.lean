-- Prove2me | Theorems.Thm_QuerySampleRev_cdf_displays
-- name    : QuerySampleRev.cdf_displays
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:36:49.075055+00:00
-- url     : https://prove2.me/theorems/32d9238a-bb30-4d73-91cf-82e667938aa6
-- title:
--   §5.5 (proof of Theorem 21) — the CDFs of $F^{(0)}$ and $F^{(i)}$; $F^{(i)}=F^{(0)}$ outside $P^{(i)}$ and $F^{(i)}(P^{(i)})=F^{(0)}(P^{(i)})$
-- statement:
--   Let $c\in[0,1]$ and $0<\varepsilon\le1/128$, with $K,\rho,a_i,m_i,b_i,P^{(i)}$ as in the construction. The base distribution $F^{(0)}$ (density $1/p^2$ on $(1,e)$, atom $1/e$ at $e$) and, for each $i\in[K]$, the hard distribution $F^{(i)}$ are probability distributions on $[0,\infty)$ whose left-continuous CDFs are
--   $$
--   F^{(0)}(p)=\begin{cases}0,&p\le1,\\ 1-1/p,&1<p\le e,\\ 1,&p>e,\end{cases}\qquad
--   F^{(i)}(p)=\begin{cases}1-\rho/a_i-(1-\rho)/p,&a_i<p\le m_i,\\ 1+\rho/a_i-(1+\rho b_i/a_i)/p,&m_i<p\le b_i,\\ F^{(0)}(p),&p\notin P^{(i)}.\end{cases}
--   $$
--   Moreover $F^{(i)}(p)=F^{(0)}(p)$ for every $p\notin P^{(i)}$ (including at the atom $e$), and $F^{(i)}$ assigns $P^{(i)}$ the same probability as $F^{(0)}$.
--
--   This ties the measures used in all later statements to the displays printed in the paper.
--
--   Differences from the source:
--   - generalization: the CDF displays for prices $p\ge0$ → the CDF identities for every real $p$; reason: for $p<0$ both sides are $0$; specializes to the source
--   - encoding: $F^{(0)}$, $F^{(i)}$ given by their CDFs → measures with explicit densities and an atom at $e$, proved to have the printed CDFs (and to be probability measures on $[0,\infty)$); reason: the measures are determined by their CDFs; the statement is the identification
-- source:
--   Jin, Tang, Wang, Zhang, Query-Sample Tradeoffs for Revenue Maximization (manuscript, sha256 c31ea3d3…), §5.5, proof of Theorem 21, p.36 (PDF p.38), the displays of F^(0) and F^(i) and the following sentence

import Mathlib
import Definitions.Def_QuerySampleRev_hardDist

open MeasureTheory
open scoped ENNReal

namespace QuerySampleRev

/-- **The CDF displays of `F⁽⁰⁾` and `F⁽ⁱ⁾`.** Jin, Tang, Wang, Zhang, *Query-Sample Tradeoffs for Revenue
Maximization* (manuscript, sha256 c31ea3d3…), §5.5, p.36 (PDF 38): "Define the base distribution by
`F⁽⁰⁾(p) ≜ 0` for `p ≤ 1`; `1 − 1/p` for `1 < p ≤ e`; `1` for `p > e`, which is the equal-revenue
distribution truncated at `e` … The corresponding CDF is `F⁽ⁱ⁾(p) ≜ 1 − ρ/a_i − (1 − ρ)/p` for
`a_i < p ≤ m_i`; `1 + ρ/a_i − (1 + ρb_i/a_i)/p` for `m_i < p ≤ b_i`; `F⁽⁰⁾(p)` for `p ∉ P⁽ⁱ⁾`. The
branches agree at `a_i, m_i, b_i`, so `F⁽ⁱ⁾` agrees with `F⁽⁰⁾` outside `P⁽ⁱ⁾`, including the atom at `e`,
and assigns the same probability to `P⁽ⁱ⁾`."

For `c ∈ [0, 1]`, `0 < ε ≤ 1/128`: `baseDist` and each `hardDist ε c i`, `i ∈ [K]`, are probability
measures on `[0, ∞)` whose left-continuous CDFs `p ↦ μ((−∞, p))` are the printed `F⁽⁰⁾` and `F⁽ⁱ⁾`; the
two agree at every `p ∉ P⁽ⁱ⁾` and give `P⁽ⁱ⁾` the same probability. -/
theorem cdf_displays {c ε : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hε0 : 0 < ε) (hε : ε ≤ 1 / 128) :
    let F0 : ℝ → ℝ := fun p => if p ≤ 1 then 0 else if p ≤ Real.exp 1 then 1 - 1 / p else 1
    let a := aPt ε c
    let m := mPt ε c
    let b := bPt ε c
    let ρ := rho ε c
    let Fi : ℕ → ℝ → ℝ := fun i p =>
      if a i < p ∧ p ≤ m i then 1 - ρ / a i - (1 - ρ) / p
      else if m i < p ∧ p ≤ b i then 1 + ρ / a i - (1 + ρ * b i / a i) / p
      else F0 p
    (IsProbabilityMeasure baseDist ∧ baseDist (Set.Iio 0) = 0 ∧
      ∀ p : ℝ, (baseDist (Set.Iio p)).toReal = F0 p) ∧
    ∀ i ∈ Finset.Icc 1 (numHard ε c),
      IsProbabilityMeasure (hardDist ε c i) ∧ hardDist ε c i (Set.Iio 0) = 0 ∧
      (∀ p : ℝ, (hardDist ε c i (Set.Iio p)).toReal = Fi i p) ∧
      (∀ p ∉ priceInterval ε c i, hardDist ε c i (Set.Iio p) = baseDist (Set.Iio p)) ∧
      hardDist ε c i (priceInterval ε c i) = baseDist (priceInterval ε c i) := by sorry

end QuerySampleRev
