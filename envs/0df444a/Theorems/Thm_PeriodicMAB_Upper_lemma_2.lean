-- Prove2me | Theorems.Thm_PeriodicMAB_Upper_lemma_2
-- name    : PeriodicMAB.Upper.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:20:52.670445+00:00
-- url     : https://prove2.me/theorems/539aca87-5568-4be5-b4e6-541337139b04
-- title:
--   Lemma 2, p. 18 — leakage bounds $\pi B_kU_1$ off the neighbourhoods and $\pi B_kU_2\le\pi B_kU_1$ inside
-- statement:
--   Let arm $k$ have mean sequence $\mu_k$ of minimum period $T_k$, Fourier coefficients $b_{k,j}$ and frequency components $\tilde\mu_{k,j}(v)=\frac1n\sum_{s=nk+1}^{n(k+1)}b_{k,j}e^{2\pi i(j/T_k-v)s}$, and suppose $g\ge\max\{2,\sqrt n\}$ is an integer with $T_k<n/(2g)$ (Assumption 3 for this arm). Then
--   $$
--   \sup_{v\in\bar{\mathcal V}_k}\Big|\sum_{j=0}^{T_k-1}\tilde\mu_{k,j}(v)\Big|\le\pi B_kU_1
--   \qquad\text{and}\qquad
--   \sup_{v\in\mathcal V_k}\Big|\sum_{j:\,|j/T_k-v|\ge g/n}\tilde\mu_{k,j}(v)\Big|\le\pi B_kU_2\le\pi B_kU_1 .
--   $$
--
--   The first bound controls the leakage of all present frequencies away from their neighbourhoods; the second controls, inside one neighbourhood, the leakage of the frequencies that lie at least $g/n$ away.
--
--   **Formalization Note** Each supremum is stated pointwise: the bound holds at every $v$ of the set. The sum in the second bound runs over all $j\in\{0,\dots,T_k-1\}$ with $|j/T_k-v|\ge g/n$; the coefficients of non-present frequencies vanish. The DFT uses the absolute epochs of the block (Step 8 of Algorithm 1).
-- source:
--   Chen, Wang and Wang, Learning and Optimization with Seasonal Patterns, arXiv:2005.08088v4, p. 18, Lemma 2

import Mathlib
import Definitions.Def_PeriodicMAB_Upper_Model
import Definitions.Def_PeriodicMAB_Upper_Spectral

open MeasureTheory ProbabilityTheory Finset
open scoped NNReal

namespace PeriodicMAB.Upper

/-- Lemma 2 (p. 18): for an arm with means `μk` of minimum period `p` satisfying the arm-wise
part of Assumption 3,
`sup_{v ∈ 𝒱̄_k} |∑_{j=0}^{p−1} µ̃_{k,j}(v)| ≤ π B_k U₁` and
`sup_{v ∈ 𝒱_k} |∑_{j : |j/p − v| ≥ g/n} µ̃_{k,j}(v)| ≤ π B_k U₂ ≤ π B_k U₁`. -/
theorem lemma_2 (μk : ℕ → ℝ) (p n g k : ℕ) (hper : IsMinPeriod μk p)
    (hA3 : Assumption3Arm n g p) :
    (∀ v ∈ nbhdVbar μk p n g,
      ‖∑ j ∈ range p, muTildeJ μk p n k j v‖ ≤ Real.pi * bigB μk p * U1 n g) ∧
    (∀ v ∈ nbhdV μk p n g,
      ‖∑ j ∈ (range p).filter (fun j : ℕ => (g : ℝ) / n ≤ |(j : ℝ) / p - v|), muTildeJ μk p n k j v‖ ≤
        Real.pi * bigB μk p * U2 n g) ∧
    Real.pi * bigB μk p * U2 n g ≤ Real.pi * bigB μk p * U1 n g := by sorry

end PeriodicMAB.Upper
