-- Prove2me | Theorems.Thm_SPOBounds_Natarajan_expected_rademacher_natarajan_bound
-- name    : SPOBounds.Natarajan.expected_rademacher_natarajan_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T18:29:44.440542+00:00
-- url     : https://prove2.me/theorems/80c7c89c-42be-4b8c-b1a6-e92f3bcc432a
-- title:
--   Theorem 2, first display — $\mathfrak R^n_{\rm SPO}(\mathcal H)\le\omega_S(\mathcal C)\sqrt{2d_N(w^*(\mathcal H))\log(n|\mathfrak S|^2)/n}$
-- statement:
--   Let $S\subseteq\mathbb R^d$ be a nonempty, compact, convex polyhedron and $\mathfrak S$ the set of its extreme points, and let $w^*$ be an optimization oracle for $S$ whose values are extreme points of $S$. Let $\mathcal C$ be a nonempty bounded set of cost vectors, let $\mathcal D$ be a probability distribution on $\mathcal X\times\mathbb R^d$ whose cost component lies in $\mathcal C$ almost surely, and let $\mathcal H$ be a family of functions $f:\mathcal X\to\mathbb R^d$. Let $k$ be a natural number such that every finite set N-shattered by $w^*(\mathcal H)$ has at most $k$ points. Then for every $n\ge1$,
--   $$\mathfrak R^n_{\rm SPO}(\mathcal H)\le\omega_S(\mathcal C)\sqrt{\frac{2k\log(n|\mathfrak S|^2)}{n}}.$$
--
--   The Rademacher complexity of $\mathcal H$ with respect to the SPO loss grows only logarithmically in the number of extreme points of $S$ and linearly (under the square root) in the Natarajan dimension of the induced decision class.
--
--   **Formalization Note** As in the empirical bound, the oracle is assumed to return extreme points (the proof's "w.l.o.g.", p. 31) and $d_N(w^*(\mathcal H))$ is replaced by an upper bound $k$ on the sizes of N-shattered sets. $\mathfrak R^n_{\rm SPO}$ is a Bochner integral over the sample; no integrability hypothesis is added because it appears only on the left-hand side (a non-integrable integrand gives the value $0$, and the right-hand side is nonnegative). The logarithm is natural.
-- source:
--   El Balghiti, Elmachtoub, Grigas, Tewari, Generalization Bounds in the Predict-then-Optimize Framework, arXiv:1905.11488v3, p. 11, Theorem 2, first display

import Mathlib
import Definitions.Def_SPOBounds_Natarajan_Model
import Definitions.Def_SPOBounds_Natarajan_Rademacher
import Definitions.Def_SPOBounds_Natarajan_NatarajanDim

open MeasureTheory

namespace SPOBounds.Natarajan

/-- **Theorem 2, first display** (arXiv:1905.11488v3, p. 11). Let `S` be a nonempty compact
convex polyhedron with extreme-point set `𝔖`, let the oracle `w` return extreme points of `S`,
and let every set N-shattered by `w*(H)` have at most `k` elements. If the cost vectors lie
almost surely in the nonempty bounded set `C`, then
`ℜⁿ_SPO(H) ≤ ω_S(C) √(2 k log(n |𝔖|²) / n)` for every `n ≥ 1`. -/
theorem expected_rademacher_natarajan_bound {d : ℕ} {X : Type*} [MeasurableSpace X]
    (S : Set (EuclideanSpace ℝ (Fin d))) (hS : S.Nonempty) (hSc : IsCompact S)
    (hSv : Convex ℝ S) (hSp : IsPolyhedron S)
    (w : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (hw : IsOracle S w)
    (hwv : ∀ c, w c ∈ Set.extremePoints ℝ S)
    (C : Set (EuclideanSpace ℝ (Fin d))) (hC : C.Nonempty) (hCb : Bornology.IsBounded C)
    (D : Measure (X × EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure D]
    (hDC : ∀ᵐ z ∂D, z.2 ∈ C)
    (H : Set (X → EuclideanSpace ℝ (Fin d)))
    (k : ℕ) (hk : ∀ T : Finset X, NShatters (oracleClass w H) T → T.card ≤ k)
    (n : ℕ) (hn : 0 < n) :
    expRademacherSPO D w H n ≤
      linGapSet S C * Real.sqrt (2 * k *
        Real.log ((n : ℝ) * ((Set.extremePoints ℝ S).ncard : ℝ) ^ 2) / n) := by sorry

end SPOBounds.Natarajan
