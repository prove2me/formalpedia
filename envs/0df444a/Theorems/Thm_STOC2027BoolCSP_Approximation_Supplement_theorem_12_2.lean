-- Prove2me | Theorems.Thm_STOC2027BoolCSP_Approximation_Supplement_theorem_12_2
-- name    : STOC2027BoolCSP.Approximation.Supplement.theorem_12_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:35:58.842038+00:00
-- url     : https://prove2.me/theorems/9e102026-f4b0-45e2-9f58-ad1badacacdc
-- title:
--   Theorem 12.2 — two-hub negative stability $L_0(f)\le1-c\|F^2\|_t^2\le1-cS_t(f)^2$
-- statement:
--   Let $k\ge4$ be even, $n=k-2$, $t=1/(16n^2)$ and $c=n(n-1)/4$. Let $N\ge0$, and let $f:\mathbb R^N\to[-1,1]$ be measurable and odd, $f(-z)=-f(z)$ for almost every $z$. Let $F$ be its Hermite generating function (50), $\|\cdot\|_u$ the Fock norm and $S_u(f)=\sum_{j\ge1}u^jW_j(f)$ as in (51). For every $t'$ with $0<t'\le t$, the quantities $\|F^2\|_{t'}^2$ and $S_{t'}(f)$ are finite and
--   $$L_0^{t'}(f)\ \le\ 1-c\,\|F^2\|_{t'}^2\ \le\ 1-c\,S_{t'}(f)^2,$$
--   where $L_0^{t'}(f)=\mathbb E\prod_{i=1}^k(1+f(G_i))$ and the rows $G_1,\dots,G_k\in\mathbb R^N$ have covariance $(I+t'A^*)\otimes I_N$, $A^*$ the two-hub matrix (hubs $1,2$, leaves $3,\dots,k$). The case $t'=t$ is (58).
--
--   The bound is uniform in the dimension $N$ and in $f$; in Section 12.3 it is combined with the positive-correlation test to give the soundness bound $\beta$ of Theorem 1.4.
--
--   Differences from the source:
--   - encoding: ‖F²‖²_t and S_t(f) as real series used when finite → values in [0, ∞]; their finiteness is part of the conclusion and the inequalities use the real values; reason: no junk value for a divergent series
--   - encoding: the same statement with any 0 < t′ ≤ t in place of t, c unchanged → one statement quantified over t′ ∈ (0, t], t′ = t included, with t′ in the covariance, the norm and S; reason: (58) is the case t′ = t
--   - encoding: hubs 1, 2 and leaves 3, …, k; covariance (I + tA*) ⊗ I_N → 0-based indices 0, 1 and 2, …, k − 1; N independent columns N(0, I + t′A*) in ℝ^k; reason: Lean indexing and the product structure of the covariance
--   - encoding: f odd almost everywhere → f(−z) = −f(z) for Lebesgue-almost every z ∈ ℝ^N; reason: Lebesgue and standard Gaussian measure have the same null sets
-- source:
--   Zhijie Zheng, Yucong He, Chengzhi Xie, Approximation and Even Arity Hardness for Boolean Constraint Satisfaction, STOC 2027 submission #40 (October 2026), printed p. 27 (PDF 30), Theorem 12.2 with equation (58); standing assumptions printed p. 22, 24 (PDF 25, 27); objects (47), (50)–(51)

import Mathlib
import Definitions.Def_STOC2027BoolCSP_Approximation_Supplement_Constants
import Definitions.Def_STOC2027BoolCSP_Approximation_Supplement_Fock
import Definitions.Def_STOC2027BoolCSP_Approximation_Supplement_TwoHub

namespace STOC2027BoolCSP.Approximation.Supplement

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- Theorem 12.2 (two-hub negative stability), printed p. 27. Let `k ≥ 4` be even, `n = k − 2`,
`t = 1/(16n²)`, `c = n(n−1)/4`. For every `N`, every measurable `f : ℝ^N → [−1, 1]` that is odd
almost everywhere, and every `0 < t' ≤ t`: `‖F²‖²_{t'}` and `S_{t'}(f)` are finite and
`L_0^{t'}(f) ≤ 1 − c‖F²‖²_{t'} ≤ 1 − c S_{t'}(f)²`, where `F` is the Hermite generating function of
`f` and `L_0^{t'}` the two-hub acceptance with covariance `(I + t'A*) ⊗ I_N`. -/
theorem theorem_12_2 (k : ℕ) (hk : 4 ≤ k) (heven : Even k) (N : ℕ) (f : (Fin N → ℝ) → ℝ)
    (hf : Measurable f) (hbd : ∀ z, |f z| ≤ 1)
    (hodd : ∀ᵐ z ∂(volume : Measure (Fin N → ℝ)), f (-z) = -f z)
    (t' : ℝ) (ht'0 : 0 < t') (ht' : t' ≤ (tC k : ℝ)) :
    fockNormSq (genSeries f ^ 2) t' ≠ ∞ ∧ stab f t' ≠ ∞ ∧
    twoHubAcc k t' f ≤ 1 - (cC k : ℝ) * (fockNormSq (genSeries f ^ 2) t').toReal ∧
    1 - (cC k : ℝ) * (fockNormSq (genSeries f ^ 2) t').toReal ≤
      1 - (cC k : ℝ) * (stab f t').toReal ^ 2 := by sorry

end STOC2027BoolCSP.Approximation.Supplement
