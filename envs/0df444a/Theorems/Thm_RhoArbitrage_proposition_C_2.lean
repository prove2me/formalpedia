-- Prove2me | Theorems.Thm_RhoArbitrage_proposition_C_2
-- name    : RhoArbitrage.proposition_C_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T04:24:49.846282+00:00
-- url     : https://prove2.me/theorems/9c42eef5-698f-4ff0-a53f-a573c725ed5f
-- title:
--   Proposition C.2, p.25 — minima of a nondecreasing sequence of lsc functions on a compact set
-- statement:
--   Let $K$ be compact and let $f_t:K\to[-\infty,\infty]$ be a nondecreasing sequence of lower semi-continuous functions with $f(x):=\lim_{t\to\infty}f_t(x)$ for all $x\in K$. Then
--
--   $$
--   \min_{x\in K}f(x)=\lim_{t\to\infty}\min_{x\in K}f_t(x).
--   $$
--
--   Furthermore, if $(x_t)_{t\ge1}$ is a sequence with $\min_{x\in K}f_t(x)=f_t(x_t)$, then any limit point of $(x_t)$ is a minimiser of $f$.
--
--   This is the exchange of limit and minimum that identifies $\rho^\infty_1$ with the limit of $\rho_t/t$.
--
--   **Formalization Note** Attainment of each minimum is stated explicitly.
--
--   Differences from the source:
--   - encoding: K ⊂ X compact, X a topological space, f_t : K → [−∞, ∞] → a type `K` with `[TopologicalSpace K] [CompactSpace K] [Nonempty K]`; reason: the functions live on K, so only the subspace topology matters; every compact subset of a space is such a type, and "min" presupposes K ≠ ∅
--   - encoding: min_{x∈K} in the display → explicit attainment (`IsMinOn`) together with `⨅ x, _`; reason: the printed min asserts attainment, and then it equals the infimum
--   - encoding: limit point of (x_t) → `MapClusterPt y atTop xs`; reason: a limit point of a sequence is a cluster point
--   - encoding: indices t ≥ 1 → indices `t : ℕ`; reason: a shift of the index
-- source:
--   Herdegen, Khan, ρ-arbitrage and ρ-consistent pricing for star-shaped risk measures, arXiv:2202.07610v3, Proposition C.2, p.25

import Mathlib

open Filter Topology

namespace RhoArbitrage

/-- **Proposition C.2 (minima of an increasing sequence of lsc functions).** Herdegen–Khan,
arXiv:2202.07610v3, Proposition C.2, p.25.

Let `K` be compact and `f_t : K → [-∞, ∞]` a nondecreasing sequence of lower semi-continuous
functions with pointwise limit `F`. Then `min_K F = lim_t min_K f_t`; and if `(x_t)` is a sequence
with `min_K f_t = f_t(x_t)`, then any limit point of `(x_t)` is a minimiser of `F`.

**Formalization Note.** The functions live on `K` as printed, so `K` is a type carrying the
compact topology; a compact subset `K ⊂ X` of a topological space, with its subspace topology, is
an instance. "`min`" presupposes `K ≠ ∅`, hence `[Nonempty K]`. The first two conjuncts are the
attainment of the minima that the printed `min` asserts, and each `min` in the display is then the
infimum `⨅ x, _`. A limit point is a cluster point (`MapClusterPt`). The paper indexes by `t ≥ 1`,
Lean by `t : ℕ`. -/
theorem proposition_C_2 {K : Type*} [TopologicalSpace K] [CompactSpace K] [Nonempty K]
    (f : ℕ → K → EReal) (F : K → EReal) (hlsc : ∀ t, LowerSemicontinuous (f t))
    (hmono : ∀ x, Monotone (fun t => f t x))
    (hlim : ∀ x, Tendsto (fun t => f t x) atTop (𝓝 (F x))) :
    (∀ t, ∃ x, IsMinOn (f t) Set.univ x) ∧
    (∃ x, IsMinOn F Set.univ x) ∧
    Tendsto (fun t => ⨅ x, f t x) atTop (𝓝 (⨅ x, F x)) ∧
    ∀ xs : ℕ → K, (∀ t, IsMinOn (f t) Set.univ (xs t)) →
      ∀ y, MapClusterPt y atTop xs → IsMinOn F Set.univ y := by sorry

end RhoArbitrage
