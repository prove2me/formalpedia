-- Prove2me | Theorems.Thm_TopicalIrreducibility_Relations_irreducibility_relations
-- name    : TopicalIrreducibility.Relations.irreducibility_relations
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:09:30.591773+00:00
-- url     : https://prove2.me/theorems/e104338f-b33b-4ed5-9d95-21d86291926a
-- title:
--   Theorem 2.4 — facial/graphical irreducibility and indecomposability of m-topical maps
-- statement:
--   Fix a finite dimension $n$. Let $f:\mathbb R^n_{\ge0}\to\mathbb R^n_{\ge0}$ be an m-topical map (continuous, order-preserving, homogeneous, with $f(\mathbb R^n_{>0})\subseteq\mathbb R^n_{>0}$). Then:
--
--   1. if $f$ is facially irreducible or graphically irreducible, then $f$ is indecomposable;
--   2. if $f$ is m-convex and indecomposable, then $f$ is graphically irreducible;
--   3. if $f$ is subadditive and indecomposable, then $f$ is facially irreducible.
--
--   In symbols,
--   $$
--   (\mathrm{FI}\vee\mathrm{GI})\Rightarrow\mathrm{Ind},\qquad (\text{m-convex}\wedge\mathrm{Ind})\Rightarrow\mathrm{GI},\qquad (\text{subadditive}\wedge\mathrm{Ind})\Rightarrow\mathrm{FI}.
--   $$
--
--   Here $\mathrm{FI}$, $\mathrm{GI}$ and $\mathrm{Ind}$ abbreviate facial irreducibility, graphical irreducibility and indecomposability, respectively. Facial irreducibility means no nontrivial proper closed face $F_J$ of the cone is invariant; graphical irreducibility means the Gaubert–Gunawardena graph $G(f)$, with an arc $i\to j$ when $f(\mathbf 1+te_{\{j\}})_i\to\infty$ as $t\to\infty$, is strongly connected; The vector $\mathbf 1$ has every entry equal to $1$, and $e_J$ is the indicator vector of $J$. Indecomposability means that for every nonempty proper $J\subset[n]$ some coordinate $i\notin J$ has $f(\mathbf 1+te_J)_i\to\infty$.
--
--   The theorem organizes the irreducibility notions for nonlinear Perron–Frobenius theory: indecomposability is the weakest, it coincides with graphical irreducibility for m-convex maps, and all three coincide for subadditive maps (which are m-convex by Lemma 1.4).
--
--   **Formalization Note** The same arbitrary m-topical $f$ appears in all three clauses; m-convexity and subadditivity are premises of clauses 2 and 3 only. The dimension $n$ is arbitrary, including $n=0$ and $n=1$, where there is no nonempty proper subset of $[n]$ and every clause holds.
--
--   Differences from the source:
--   - generalization: the dimension-zero case is not discussed → every n : Nat, including n = 0; reason: there are no nonempty proper coordinate subsets or vertices at n = 0, so all three predicates hold; every positive-dimensional source instance is retained.
--   - encoding: real nonnegative coordinate vectors indexed by 1,...,n, and subsets of these indices → Fin n → ℝ≥0 with its product topology and pointwise operations; subsets are Finset (Fin n); reason: the coordinates are relabeled from 1-based to 0-based; the type represents the entire closed real cone, and positive NNReal scalars represent all positive real scalars.
--   - encoding: the limit of each outside coordinate ray is finite → for each outside coordinate i there exists B : ℝ≥0 bounding f(1 + t e_J)_i for every t : ℝ≥0; reason: order preservation makes each full nonnegative-real ray monotone, so boundedness is equivalent to convergence to a finite limit; restricting t to the nonnegative reals changes no limit at positive infinity.
--   - encoding: the directed graph is strongly connected → every ordered pair is related by Relation.ReflTransGen of the source arc relation; reason: this is directed reachability by possibly empty paths, preserving the usual singleton-vertex convention and the source arc orientation.
-- source:
--   Brian Lins, Irreducibility for Topical Maps, STOC 2027 submission #201 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/201.pdf, p. 4, Theorem 2.4 (proof pp. 4–5); PDF page = printed page

import Mathlib
import Definitions.Def_TopicalIrreducibility_Relations_MTopical
import Definitions.Def_TopicalIrreducibility_Relations_Irreducibility

open scoped NNReal

namespace TopicalIrreducibility.Relations

/-- Theorem 2.4 (Lins, p. 4). Let `f : ℝⁿ_{≥0} → ℝⁿ_{≥0}` be m-topical.
(1) facially or graphically irreducible ⇒ indecomposable;
(2) m-convex and indecomposable ⇒ graphically irreducible;
(3) subadditive and indecomposable ⇒ facially irreducible. -/
theorem irreducibility_relations {n : ℕ} (f : StdCone n → StdCone n) (hf : IsMTopical f) :
    ((FaciallyIrreducible f ∨ GraphicallyIrreducible f) → Indecomposable f) ∧
    (IsMConvex f → Indecomposable f → GraphicallyIrreducible f) ∧
    (IsSubadditive f → Indecomposable f → FaciallyIrreducible f) := by sorry

end TopicalIrreducibility.Relations
