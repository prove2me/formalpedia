-- Prove2me | Theorems.Thm_PredAdvice_rs_stability
-- name    : PredAdvice.rs_stability
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:34:10.345896+00:00
-- url     : https://prove2.me/theorems/0c8fc936-8868-4ded-bba9-64e4caa2f41d
-- title:
--   Constant-scale stability of $RS$
-- statement:
--   1. For every constant $C\ge1$ there is $K>0$ such that for all integers $2\le q\le N\le Cq$,
--   $$
--   RS(N)\le K\,RS(q)\quad\text{and}\quad RS(q)\le K\,RS(N),
--   $$
--   that is, $RS(N)=\Theta_C(RS(q))$.
--   2. For all constants $C_1,C_2$ there is $K$ such that, for every $q\ge2$, every simple graph on at most $C_1q$ vertices whose edges are partitioned into at most $C_2q$ induced matchings has at most $K\,q^2/RS(q)$ edges.
--
--   Clause 2 is how Lemma 3.5 bounds the bipartite graphs $G^j_{d,c}$, which have $2n$ vertices and at most $n$ matching classes.
--
--   Differences from the source:
--   - encoding: Θ_C and O(·) with constants depending on C, C₁, C₂ → explicit constants K chosen after C (resp. C₁, C₂) and before q, N and the graph; reason: same statement
--   - encoding: a graph on O(q) vertices → a simple graph on any finite type with at most C₁q vertices; reason: same statement; Lemma 3.5 applies it to two copies of V
-- source:
--   Kopelowitz, Korin, Roditty, Using Small Advice to Compress the Predecessor Matrix, STOC 2027 submission (manuscript sha256 0ae8a68d…), §2, p.10, with footnote 9

import Mathlib
import Definitions.Def_PredAdvice_RS

set_option autoImplicit false

namespace PredAdvice

/-- **Constant-scale stability of RS** (Kopelowitz, Korin, Roditty, *Using Small Advice to Compress the Predecessor Matrix*, STOC 2027 submission (manuscript sha256 0ae8a68d…), §2, p.10, with footnote 9):

1. for every fixed `C ≥ 1` and integers `2 ≤ q ≤ N ≤ Cq`, `RS(N) = Θ_C(RS(q))`;
2. any graph on `O(q)` vertices whose edges can be partitioned into `O(q)` induced matchings has
   `O(q²/RS(q))` edges.

**Formalization Note** `Θ_C`: a constant `K > 0` depending only on `C` with
`RS(N) ≤ K·RS(q)` and `RS(q) ≤ K·RS(N)`. In clause 2 the `O(q)` are `C₁q` vertices and `C₂q`
colour classes, and the `O(·)` constant `K` depends only on `C₁, C₂`; the graph lives on any finite
type (in Lemma 3.5 it is a bipartite graph on two copies of `V`). -/
theorem rs_stability :
    (∀ C : ℝ, 1 ≤ C → ∃ K : ℝ, 0 < K ∧ ∀ q N : ℕ, 2 ≤ q → q ≤ N → (N : ℝ) ≤ C * q →
        RS N ≤ K * RS q ∧ RS q ≤ K * RS N) ∧
    (∀ C₁ C₂ : ℝ, ∃ K : ℝ, ∀ q : ℕ, 2 ≤ q → ∀ (W : Type*) [Fintype W] (G : SimpleGraph W)
        (m : ℕ) (col : G.edgeSet → Fin m), (Fintype.card W : ℝ) ≤ C₁ * q → (m : ℝ) ≤ C₂ * q →
        IsInducedMatchingColoring G col →
        (G.edgeSet.ncard : ℝ) ≤ K * ((q : ℝ) ^ 2 / RS q)) := by sorry

end PredAdvice
