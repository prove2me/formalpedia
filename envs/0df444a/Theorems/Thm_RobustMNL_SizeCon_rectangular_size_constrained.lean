-- Prove2me | Theorems.Thm_RobustMNL_SizeCon_rectangular_size_constrained
-- name    : RobustMNL.SizeCon.rectangular_size_constrained
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T14:21:29.458693+00:00
-- url     : https://prove2.me/theorems/c6dcb8e3-5604-4cd2-8c03-9d19e903deb4
-- title:
--   Theorem 3.8 — for V = ∏_{i=0}^n [l_i, u_i], Y*(V) = max_{S⊆A:|S|≤K} f(S, (u₀, l₁, …, lₙ))
-- statement:
--   **Theorem 3.8 (Robust size-constrained assortment under rectangular uncertainty sets).** Let $\mathcal A=\{1,\dots,n\}$ be a set of products with real revenues $r_1,\dots,r_n$, and let $K\in\mathbb N$ be the largest allowable assortment size. Let $\mathcal V=\prod_{i=0}^n [l_i,u_i]\subseteq\mathbb R^{n+1}_{++}$ be a rectangular uncertainty set for the MNL parameters $v=(v_0,v_1,\dots,v_n)$: $0<l_0\le u_0$ and $0<l_i\le u_i$ for each product $i$. Then
--
--   $$
--   Y^*(\mathcal V)=\max_{S\subseteq\mathcal A:\ |S|\le K}\ \min_{v\in\mathcal V} f(S,v)
--   =\max_{S\subseteq\mathcal A:\ |S|\le K}\ \frac{\sum_{i\in S} l_i r_i}{u_0+\sum_{i\in S} l_i}
--   =\max_{S\subseteq\mathcal A:\ |S|\le K} f\big(S,(u_0,l_1,l_2,\dots,l_n)\big).
--   $$
--
--   The size-constrained robust problem appears intractable for a general uncertainty set; over a box it reduces to a size-constrained assortment problem with the known weights $(u_0,l_1,\dots,l_n)$, which can be solved efficiently.
--
--   **Formalization Note** Both maxima range over all subsets of size at most $K$ (any $K\in\mathbb N$, including $K=0$ and $K\ge n$), and the minimum over the whole box, as a real infimum. The middle expression is $f(S,(u_0,l))$ written out, so the Lean statement is the single equality between the left and right ends. The hypotheses $l_0\le u_0$, $l\le u$ say the intervals are nonempty (the paper's intervals are ranges of likely values); $0<l_0$, $0<l_i$ express $\prod[l_i,u_i]\subset\mathbb R^{n+1}_{++}$. Revenues are arbitrary reals; the paper's ordering $r_1\ge\dots\ge r_n>0$ is used by no proof and is dropped, a strengthening. Products are 0-indexed (`Fin n`).
-- source:
--   Rusmevichientong, Topaloglu, Robust Assortment Optimization in Revenue Management Under the Multinomial Logit Choice Model, Operations Research (2012), doi:10.1287/opre.1120.1063, authors' manuscript of 20 Sep 2011, Theorem 3.8, p. 11

import Mathlib
import Definitions.Def_ChoiceCDLP_MNL_mnlObjective
import Definitions.Def_RobustMNL_SizeCon_Model

namespace RobustMNL.SizeCon

/-- Theorem 3.8, p. 11 (Robust Size-Constrained Assortment under Rectangular Uncertainty Sets):
for `V = ∏_{i=0}^n [l_i, u_i] ⊆ ℝⁿ⁺¹₊₊`,
`Y*(V) = max_{S ⊆ 𝒜 : |S| ≤ K} f(S, (u₀, l₁, …, lₙ))`. -/
theorem rectangular_size_constrained {n : ℕ} (l₀ u₀ : ℝ) (l u : Fin n → ℝ) (hl₀ : 0 < l₀)
    (hlu₀ : l₀ ≤ u₀) (hl : ∀ i, 0 < l i) (hlu : l ≤ u) (r : Fin n → ℝ) (K : ℕ) :
    Ystar (box l₀ u₀ l u) r K = knownMax r K (u₀, l) := by sorry

end RobustMNL.SizeCon
