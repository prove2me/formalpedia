-- Prove2me | Theorems.Thm_ProdMomentConc_readFamily_mgf_le
-- name    : ProdMomentConc.readFamily_mgf_le
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:12:14.106169+00:00
-- url     : https://prove2.me/theorems/a6500409-573a-43bf-9626-8a29454987fe
-- title:
--   Proof of Theorem 3.1, first display — exponential moment of a read-$d$ family with mean $p$
-- statement:
--   Let $X_1,\dots,X_m$ be mutually independent Boolean random variables, and let $Y_i = f_i(X_{P_i}) \in [0,1]$, $i = 1,\dots,k$, be outputs with $\mathbb E[Y_i] = p$ for all $i$ that form a read-$d$ family ($d \ge 1$: every underlying variable is read by at most $d$ of the outputs). Then for every $\lambda > 0$,
--
--   $$
--   \mathbb E\Big[\exp\Big(\lambda \sum_{i=1}^k Y_i\Big)\Big] \le \Big(\prod_{i=1}^k \mathbb E\big[e^{\lambda d Y_i}\big]\Big)^{1/d} \le \big(1 - p + p e^{\lambda d}\big)^{k/d}.
--   $$
--
--   The first inequality is Lemma 2.5 applied to $F_i = e^{\lambda Y_i}$; the second bounds the exponential moment of a $[0,1]$-valued variable by that of a Bernoulli variable with the same mean. In the paper the display is applied to the outputs in a random $k$-subset whose underlying variables are independent by $r$-wise independence; it supplies the "good term" of every bound in the mission.
--
--   **Formalization Note** The outputs are indexed by `Fin k`; $\lambda$ is called `t`; both inequalities are stated as a conjunction.
--
--   Differences from the source:
--   - generalization: the display concerns the induced subfamily Y_{i_1},…,Y_{i_k} of the regular setting, whose underlying bits are independent by r-wise independence, with d = d_L → any read-d family of k outputs in [0,1] with common mean p over mutually independent Boolean bits; reason: the paper's case is the instance given by the sampled outputs and the bits they read
-- source:
--   Saks, Srinivasan, Valieva, Concentration from Product Moments via an Additional Element of Randomness, arXiv:2608.04125 (held version, sha256 5218e9d0405f975413d3e2dd2c4c9d6b43c772029e645965afee1cd619ae38aa), proof of Theorem 3.1, first display, p.12 (PDF p.12)

import Mathlib

open MeasureTheory ProbabilityTheory

namespace ProdMomentConc

/-- **Exponential moment of a read-`d` family with common mean `p`** (proof of Theorem 3.1, first
display).
Saks, Srinivasan, Valieva, *Concentration from Product Moments via an Additional Element of
Randomness*, arXiv:2608.04125 (held version, sha256 5218e9d0…), proof of Theorem 3.1, p.12: "Since the induced family Yi1, . . . , Yik is read-dL, by Lemma
2.5 we have E[exp(λ ∑ⱼ Yij)] ≤ (∏ⱼ E[e^{λdL Yij}])^{1/dL} ≤ (1 − p + pe^{λdL})^{k/dL}".

For `k` outputs `Yᵢ = fᵢ(X_{Pᵢ}) ∈ [0, 1]` with `E[Yᵢ] = p`, forming a read-`d` family (`d ≥ 1`)
over independent Boolean bits, and `λ > 0`:
`E[exp(λ ∑ᵢ Yᵢ)] ≤ (∏ᵢ E[e^{λ d Yᵢ}])^{1/d} ≤ (1 − p + p e^{λd})^{k/d}`.

**Formalization Note.** The display is stated as the general lemma it instantiates: the family is
indexed by `Fin k`, the bits are mutually independent (`iIndepFun`; in the paper this comes from
r-wise independence and `|Γ(I)| ≤ r`), and the degree bound is a natural number `d` (the paper's
`dL`, an integer in the regular case). `λ` is called `t`. Both inequalities of the display are
stated. -/
theorem readFamily_mgf_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {m k : ℕ} (X : Fin m → Ω → Bool) (hXm : ∀ j, Measurable (X j)) (hX : iIndepFun X μ)
    (P : Fin k → Finset (Fin m)) (f : (i : Fin k) → (P i → Bool) → ℝ)
    (hf : ∀ i b, 0 ≤ f i b ∧ f i b ≤ 1) (p : ℝ)
    (hmean : ∀ i, ∫ ω, f i (fun j => X j ω) ∂μ = p)
    (d : ℕ) (hd : 1 ≤ d) (hread : ∀ j, (Finset.univ.filter (fun i => j ∈ P i)).card ≤ d)
    (t : ℝ) (ht : 0 < t) :
    ∫ ω, Real.exp (t * ∑ i, f i (fun j => X j ω)) ∂μ ≤
        (∏ i, ∫ ω, Real.exp (t * (d : ℝ) * f i (fun j => X j ω)) ∂μ) ^ (1 / (d : ℝ)) ∧
      (∏ i, ∫ ω, Real.exp (t * (d : ℝ) * f i (fun j => X j ω)) ∂μ) ^ (1 / (d : ℝ)) ≤
        (1 - p + p * Real.exp (t * (d : ℝ))) ^ ((k : ℝ) / (d : ℝ)) := by sorry

end ProdMomentConc
