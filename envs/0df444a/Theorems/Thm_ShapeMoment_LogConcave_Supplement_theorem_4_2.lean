-- Prove2me | Theorems.Thm_ShapeMoment_LogConcave_Supplement_theorem_4_2
-- name    : ShapeMoment.LogConcave.Supplement.theorem_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T22:10:24.965686+00:00
-- url     : https://prove2.me/theorems/6cede653-f0c1-49a9-8b10-e4c9eb3f8735
-- title:
--   Theorem 4.2, p. 16 (corrected: positive pieces end at the last positive index; plateau and zero tail separate; at most m pieces) — IFR optimal extreme points
-- statement:
--   Consider (DMP-IFR′) with $n$ support points $w_j=j$, moments $q_0=1,q_1,\dots,q_m$ and arbitrary real objective coefficients $f_1,\dots,f_n$, and suppose its feasible region is nonempty. Then
--
--   1. (DMP-IFR′) has an optimal extreme point $y^*$ (an extreme point of the feasible region that maximizes $\sum_j f_j(y_j-y_{j+1})$ over it);
--   2. every optimal extreme point $y^*$ has the following form. There are integers $1\le j_1\le k\le n$ and $s\le m$ such that
--   $$y^*_j=1\ (1\le j\le j_1),\qquad 1=y^*_{j_1}>y^*_{j_1+1}>\dots>y^*_k>0,\qquad y^*_j=0\ (j>k),$$
--   and breakpoints $j_1=b_0<b_1<\dots<b_s=k$ with parameters $\alpha_i>0$, $0<r_i<1$ ($i\in[1,s]$) such that
--   $$y^*_j=\alpha_i\,r_i^{\,j-b_{i-1}}\qquad\text{for } j\in[b_{i-1},b_i].$$
--
--   In the paper's notation $j_2=k+1$ is the first index of the zero tail ($j_2=n+1$ when $y^*$ has no zero), and the decreasing part consists of at most $m$ geometric pieces. When $j_1=k$ there are no pieces ($s=0$): $y^*$ is an all-one plateau followed by zeros, i.e. the distribution is a point mass.
--
--   The theorem is the IFR counterpart of Theorem 4.1: an optimal IFR distribution for a moment problem can be searched among distributions whose tail is flat, then piecewise geometric with at most $m$ pieces, then zero.
--
--   **Formalization Note** Indices are one-based through the zero extension `ext` of the base mission; $y_{n+1}=0$. The standing normalization $q_0=1$ (p. 5) is a hypothesis; with the convention $w_0^i=0$ at every order it gives $y_1=1$.
--
--   Differences from the source:
--
--   - correction: (18) has pieces on [u_i, v_i] up to v_m = j_2 with y_{j_2} = 0, and "0 otherwise" also before j_1 → the pieces cover [j_1, k] with k = j_2 − 1 the last positive index, y = 1 on [1, j_1] and y = 0 after k as separate branches; reason: as printed the statement is false for every optimal extreme point with a zero entry or with j_1 > 1. Counterexample: n = 3, m = 1, q = (1, 3/2), f = 0; y* = (1, 1/2, 0) is an extreme point of the feasible segment {(1, 1/2 − u, u) : 0 ≤ u ≤ 1 − √3/2} and is optimal, but (18) would need y*_{j_2} = α_1 r_1^{j_2 − 1} > 0 at the zero entry. Likewise q = (1, 2) gives the optimal extreme point (1, 1, 0), where any j_1 ≥ 2 puts y*_1 = 1 under "0 otherwise" and j_1 = 1 forces y*_2 = r_1 < 1. Appendix A.7 (p. 28) fixes k = j_2 − 1 as the last positive index and counts the pieces on [j_1, k] (p. 29)
--   - correction: exactly m pieces with u_1 < v_1 < … < v_m → s ≤ m pieces with strictly increasing breakpoints, s = 0 when j_1 = k; reason: a point mass has no room for a nondegenerate piece, e.g. y* = (1, 1, 0) above with m = 1; the proof on p. 29 bounds the number of breaks by m − 1, i.e. at most m pieces, and Theorem 4.1 says "(at most) m pieces"
--   - reading: the strictly decreasing middle part "1 = y_{j_1} > ⋯" (p. 16, above the theorem) → stated as a conclusion; reason: it follows from 0 < r_i < 1 and is part of the three-interval description the theorem refines
--   - encoding: "w_0^j are set to 0" → w_0^i = 0 for every order i, including i = 0; reason: the superscript j is a slip for the moment order i, and with 0^0 = 1 the zeroth equation would lose the normalization y_1 = 1 used in A.7
-- source:
--   Chen, He, Jiang, Ryan & Zhang, The discrete moment problem with nonconvex shape constraints, arXiv:1708.02079v1, p. 16, Theorem 4.2 and (18); (DMP-IFR′) on p. 7; proof in Appendix A.7, pp. 28–29

import Definitions.Def_ShapeMoment_LogConcave_Supplement_IFRModel

namespace ShapeMoment.LogConcave.Supplement

theorem theorem_4_2 (n m : ℕ) (f : Fin n → ℝ) (q : ℕ → ℝ)
    (hq0 : q 0 = 1) (hfeas : (feasIFRPrime n m q).Nonempty) :
    (∃ y ∈ (feasIFRPrime n m q).extremePoints ℝ,
      IsIFRMaxSol f (feasIFRPrime n m q) y) ∧
    ∀ y ∈ (feasIFRPrime n m q).extremePoints ℝ,
      IsIFRMaxSol f (feasIFRPrime n m q) y →
      ∃ (a k s : ℕ) (b : Fin (s + 1) → ℕ) (α r : Fin s → ℝ),
        1 ≤ a ∧ a ≤ k ∧ k ≤ n ∧ s ≤ m ∧
        (∀ j, 1 ≤ j → j ≤ a → ext y j = 1) ∧
        (∀ j, a ≤ j → j < k → ext y (j + 1) < ext y j) ∧
        (∀ j, 1 ≤ j → j ≤ k → 0 < ext y j) ∧
        (∀ j, k < j → ext y j = 0) ∧
        StrictMono b ∧ b 0 = a ∧ b (Fin.last s) = k ∧
        (∀ i, 0 < α i ∧ 0 < r i ∧ r i < 1) ∧
        (∀ i : Fin s, ∀ j, b i.castSucc ≤ j → j ≤ b i.succ →
          ext y j = α i * r i ^ (j - b i.castSucc)) := by sorry

end ShapeMoment.LogConcave.Supplement
