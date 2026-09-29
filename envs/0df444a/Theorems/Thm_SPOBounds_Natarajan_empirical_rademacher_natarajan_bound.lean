-- Prove2me | Theorems.Thm_SPOBounds_Natarajan_empirical_rademacher_natarajan_bound
-- name    : SPOBounds.Natarajan.empirical_rademacher_natarajan_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T18:29:16.655378+00:00
-- url     : https://prove2.me/theorems/1c5afc08-97c0-474d-9599-5e90f26b7162
-- title:
--   Proof of Theorem 2 (App. B.1) — empirical bound $\hat{\mathfrak R}^n_{\rm SPO}(\mathcal H)\le\omega_S(\mathcal C)\sqrt{2d_N\log(n|\mathfrak S|^2)/n}$
-- statement:
--   Let $S\subseteq\mathbb R^d$ be a nonempty, compact, convex polyhedron and $\mathfrak S$ the (finite) set of its extreme points. Let $w^*$ be an optimization oracle for $S$ whose values are extreme points of $S$. Let $\mathcal C$ be a nonempty bounded set of cost vectors and $\mathcal H$ a family of functions $f:\mathcal X\to\mathbb R^d$, and let $k$ be a natural number such that every finite set N-shattered by $w^*(\mathcal H)$ has at most $k$ points (so $k\ge d_N(w^*(\mathcal H))$). Then for every sample $(x_1,c_1),\dots,(x_n,c_n)$ with $n\ge1$ and every $c_i\in\mathcal C$,
--   $$\hat{\mathfrak R}^n_{\rm SPO}(\mathcal H)\le\omega_S(\mathcal C)\sqrt{\frac{2k\log(n|\mathfrak S|^2)}{n}}.$$
--
--   This is the fixed-sample bound at the end of the displayed chain in the proof of Theorem 2; combined with the Massart step it amounts to the Natarajan counting bound $|\mathfrak F_{|\mathbb X}|\le n^{k}|\mathfrak S|^{2k}$.
--
--   **Formalization Note** The hypothesis that the oracle returns extreme points is the proof's own "w.l.o.g." (p. 31: "$w^*(\cdot)$ has at most $|\mathfrak S|$ possible values w.l.o.g."), made explicit because p. 10 allows the oracle to return a non-extreme optimal point in case of ties. The Natarajan dimension $d_N$ is replaced by any upper bound $k$ on the sizes of N-shattered sets; taking $k=d_N$ recovers the printed statement when $d_N$ is finite, and the printed bound is vacuous when $d_N=\infty$. $|\mathfrak S|$ is `Set.ncard` of the extreme points, finite for a bounded polyhedron. The logarithm is natural.
-- source:
--   El Balghiti, Elmachtoub, Grigas, Tewari, Generalization Bounds in the Predict-then-Optimize Framework, arXiv:1905.11488v3, p. 31, Appendix B.1 (proof of Theorem 2), the displayed chain, last line

import Mathlib
import Definitions.Def_SPOBounds_Natarajan_Model
import Definitions.Def_SPOBounds_Natarajan_Rademacher
import Definitions.Def_SPOBounds_Natarajan_NatarajanDim

namespace SPOBounds.Natarajan

/-- **Proof of Theorem 2, empirical bound** (arXiv:1905.11488v3, Appendix B.1, p. 31, the
displayed chain, last line). Let `S` be a nonempty compact convex polyhedron with extreme-point
set `𝔖`, let the oracle `w` return extreme points of `S`, and let every set N-shattered by
`w*(H)` have at most `k` elements. For every sample `s` of size `n ≥ 1` whose cost vectors lie
in the nonempty bounded set `C`,
`R̂ⁿ_SPO(H) ≤ ω_S(C) √(2 k log(n |𝔖|²) / n)`. -/
theorem empirical_rademacher_natarajan_bound {d : ℕ} {X : Type*}
    (S : Set (EuclideanSpace ℝ (Fin d))) (hS : S.Nonempty) (hSc : IsCompact S)
    (hSv : Convex ℝ S) (hSp : IsPolyhedron S)
    (w : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (hw : IsOracle S w)
    (hwv : ∀ c, w c ∈ Set.extremePoints ℝ S)
    (C : Set (EuclideanSpace ℝ (Fin d))) (hC : C.Nonempty) (hCb : Bornology.IsBounded C)
    (H : Set (X → EuclideanSpace ℝ (Fin d)))
    (k : ℕ) (hk : ∀ T : Finset X, NShatters (oracleClass w H) T → T.card ≤ k)
    (n : ℕ) (hn : 0 < n) (s : Fin n → X × EuclideanSpace ℝ (Fin d)) (hsC : ∀ i, (s i).2 ∈ C) :
    empRademacherSPO w H s ≤
      linGapSet S C * Real.sqrt (2 * k *
        Real.log ((n : ℝ) * ((Set.extremePoints ℝ S).ncard : ℝ) ^ 2) / n) := by sorry

end SPOBounds.Natarajan
