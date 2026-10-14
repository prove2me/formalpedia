-- Prove2me | Theorems.Thm_ReflectedRWLDP_SamplePath_lemma_3_3
-- name    : ReflectedRWLDP.SamplePath.lemma_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T22:36:56.035958+00:00
-- url     : https://prove2.me/theorems/08868c75-ec3f-4099-a638-74a9e473de4f
-- title:
--   Lemma 3.3 — finite-dimensional LDP in $\mathbb R^k_+$ for the block sums of $W_j$, with good rate $I_{\mathbf t}$
-- statement:
--   Under the standing assumptions (i.i.d. increments with mean $\mu<0$, Assumptions 2.1–2.3, $p>0$), let $\alpha=1/(1+p)$. Let $\mathbf t=(t_1,\dots,t_k)$, $k\ge1$, with $0=t_0\le t_1<\dots<t_k\le1$ and $\Delta t_i=t_i-t_{i-1}$. Let $\mu_n$ be the law of
--   $$\Big(\frac1n\sum_{j=1}^{N(nt_1)}W_j,\ \dots,\ \frac1n\sum_{j=N(nt_{k-1})+1}^{N(nt_k)}W_j\Big).$$
--   Then $\mu_n$ satisfies the large deviation principle in $\mathbb R^k_+$ with respect to the Euclidean topology, with speed $n^\alpha$ and the good rate function
--   $$I_{\mathbf t}(x_1,\dots,x_k)=\begin{cases}\mathcal B^*_0\sum_{i=1}^k(x_i-\lambda\Delta t_i)^\alpha&\text{if }x_i\ge\lambda\Delta t_i\ \forall i,\\ \infty&\text{otherwise.}\end{cases}$$
--
--   This is the first step of the projective-limit route to the sample-path large deviation principle for $\bar Z_n$.
--
--   **Formalization Note** $\mathbb R^k_+$ carries the sup distance, which has the same topology and the same compact sets as the Euclidean distance. "Good" means lower semicontinuous with compact level sets (`MFGLimit.LDP.IsGoodRate`).
-- source:
--   Bazhba, Blanchet, Rhee & Zwart, Sample-Path Large Deviations for Unbounded Additive Functionals of the Reflected Random Walk, arXiv:2003.14381v3, p. 12, Lemma 3.3, (3.7)

import Mathlib
import Definitions.Def_BellWilliams2001_ThresholdPolicy_LargeDeviation
import Definitions.Def_MFGLimit_LDP_LDP
import Definitions.Def_ReflectedRWLDP_SamplePath_PathSpace
import Definitions.Def_ReflectedRWLDP_SamplePath_LDP
import Definitions.Def_ReflectedRWLDP_SamplePath_Model
import Definitions.Def_ReflectedRWLDP_SamplePath_RateFunction

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace ReflectedRWLDP.SamplePath

/-- **Lemma 3.3** (p. 12). For `0 = t₀ ≤ t₁ < ⋯ < t_k ≤ 1` (`k ≥ 1`), the vector
`((1/n)∑_{j=1}^{N(nt₁)} W_j, …, (1/n)∑_{j=N(nt_{k−1})+1}^{N(nt_k)} W_j)` satisfies the LDP in `ℝ^k_+` with
speed `n^α` and the good rate function `I_𝐭` of (3.7). -/
theorem lemma_3_3 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (U : ℕ → Ω → ℝ) (p : ℝ)
    (h : Standing P U p) (k : ℕ) (hk : 0 < k) (t : Fin (k + 1) → ℝ) (ht0 : t 0 = 0)
    (hmono : Monotone t) (hstrict : ∀ i j : Fin (k + 1), 0 < i → i < j → t i < t j)
    (hlast : t (Fin.last k) ≤ 1) :
    SatisfiesLDP P (blockVec U p t) edist (fun n => (n : ℝ) ^ alpha p) (rateBlock P U p t) ∧
      MFGLimit.LDP.IsGoodRate edist (rateBlock P U p t) := by sorry

end ReflectedRWLDP.SamplePath
