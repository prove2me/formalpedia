-- Prove2me | Theorems.Thm_TruncLowDeg_Recovery_fact_5_6
-- name    : TruncLowDeg.Recovery.fact_5_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T05:24:28.505507+00:00
-- url     : https://prove2.me/theorems/fea35a66-cfc5-4450-83c7-69d99da37d13
-- title:
--   Fact 5.6 — weighted Remez inequality on a convex body ([Fra09], [Gan17])
-- statement:
--   Let $V\subseteq\mathbb R^d$ be a convex body, $E\subseteq V$ measurable with positive Lebesgue measure, $r\ge0$, and $h:V\to(0,\infty)$ continuous and concave. Set
--   $$\lambda=\frac{\int_Eh(x)^r\,dx}{\int_Vh(x)^r\,dx}\in(0,1].$$
--   Then for every $k\in\mathbb N$ and $p\in\mathbb R[x]_{\le k}$,
--   $$\sup_{x\in V}|p(x)|\le T_k\Big(\frac{2}{1-(1-\lambda)^{1/(d+r)}}-1\Big)\cdot\sup_{x\in E}|p(x)| ,$$
--   where $T_k$ is the Chebyshev polynomial of degree $k$. With $h(x)=\exp(-\|x\|^2/(2r))$ it compares a polynomial on a ball with its values on a set of small Gaussian mass, which is how Lemma 5.5 is proved.
--
--   **Formalization Note.** A convex body is a compact convex set with non-empty interior. $h$ is a function on $\mathbb R^d$ that is positive, continuous and concave on $V$; $T_k$ is `Polynomial.Chebyshev.T ℝ k` (first kind).
--
--   Differences from the source:
--
--   - encoding: ℝ^d, coordinates j ∈ {1, …, d} → `Vec d = EuclideanSpace ℝ (Fin d)`, 0-based coordinates `Fin d`; reason: Lean convention; same instances
--   - reading: E ⊆ V measurable → `NullMeasurableSet E volume` (Lebesgue measurable); reason: the statement is about Lebesgue measure; Borel sets are Lebesgue measurable, so the Borel reading is covered as well
--   - encoding: the exponent 1/(d + r) → hypothesis 0 < d + r; reason: it excludes only d = r = 0, where 1/(d + r) is undefined; for d ≥ 1 it always holds
--   - encoding: h : V → (0, ∞) continuous and concave → h : ℝ^d → ℝ with h > 0 on V, `ContinuousOn h V`, `ConcaveOn ℝ V h`; reason: values outside V play no role
--   - encoding: sup_{x∈V} |p(x)|, sup_{x∈E} |p(x)| and T_k → `supAbs p V`, `supAbs p E` (real sSup of |p| over the set) and `(Polynomial.Chebyshev.T ℝ k).eval`; reason: V is compact and E is bounded and non-empty, so the suprema are finite and attained or approached; Mathlib's Chebyshev polynomial of the first kind
-- source:
--   Vári-Kakas, Wiedmer, A General Approach to Polynomial-Time Truncated Learning via Low-Degree Moments, STOC 2027 submission (manuscript sha256 613f0e39…), p. 22, Fact 5.6 ([Fra09, Corollary 5], [Gan17, Theorem 1.4])

import Definitions.Def_TruncLowDeg_Recovery_Basic

open MeasureTheory ProbabilityTheory
open scoped MatrixOrder

namespace TruncLowDeg.Recovery

/-- Fact 5.6 (p. 22, [Fra09, Corollary 5], [Gan17, Theorem 1.4]): the weighted Remez inequality.
For a convex body `V ⊆ ℝ^d` (convex, compact, non-empty interior), a Lebesgue-measurable
`E ⊆ V` of positive measure, `r ≥ 0` and a continuous concave `h : V → (0, ∞)`, with
`λ = ∫_E h^r / ∫_V h^r`: for every `k ∈ ℕ` and `p ∈ ℝ[x]_{≤k}`,
`sup_V |p| ≤ T_k(2/(1 − (1 − λ)^{1/(d+r)}) − 1) · sup_E |p|`, `T_k` the Chebyshev polynomial
of the first kind. The hypothesis `d + r > 0` only excludes the case where `1/(d + r)` is
undefined. -/
theorem fact_5_6 {d : ℕ} (V E : Set (Vec d)) (hVconv : Convex ℝ V) (hVcomp : IsCompact V)
    (hVint : (interior V).Nonempty) (hEV : E ⊆ V) (hEm : NullMeasurableSet E volume)
    (hEpos : 0 < volume E) (r : ℝ) (hr : 0 ≤ r) (hdr : 0 < (d : ℝ) + r) (h : Vec d → ℝ)
    (hpos : ∀ x ∈ V, 0 < h x) (hcont : ContinuousOn h V) (hconc : ConcaveOn ℝ V h)
    (k : ℕ) (p : MvPolynomial (Fin d) ℝ) (hp : p.totalDegree ≤ k) :
    supAbs p V ≤
      (Polynomial.Chebyshev.T ℝ (k : ℤ)).eval
        (2 / (1 - (1 - (∫ x in E, h x ^ r) / (∫ x in V, h x ^ r)) ^ (1 / ((d : ℝ) + r))) - 1) *
        supAbs p E := by sorry

end TruncLowDeg.Recovery
