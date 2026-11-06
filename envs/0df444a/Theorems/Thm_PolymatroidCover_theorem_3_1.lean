-- Prove2me | Theorems.Thm_PolymatroidCover_theorem_3_1
-- name    : PolymatroidCover.theorem_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:20:08.996878+00:00
-- url     : https://prove2.me/theorems/da63f240-ac40-4ffe-8314-2f561dcfe08b
-- title:
--   Theorem 3.1 — one more element can always be colored with $k = (2d-1)\chi^\circ(f) - (2d-2)$ colors
-- statement:
--   Let $f : 2^E \to \mathbb Z_{\ge 0}$ be a $d$-polymatroid with no self-loops ($f(e) > 0$ for every $e \in E$, the standing assumption of §2), and let
--
--   $$
--   k := (2d - 1)\cdot\chi^\circ(f) - (2d - 2).
--   $$
--
--   **Theorem 3.1.** For every $S \subseteq E$ that admits a valid $k$-coloring and every element $h \in E \setminus S$, the set $S \cup \{h\}$ admits a valid $k$-coloring.
--
--   Applied to the elements of $E$ one at a time, starting from $S = \emptyset$, it yields a covering of $E$ by $k$ independent sets: this is the existential half of Theorem 1.1.
--
--   Differences from the source:
--   - encoding: a finite ground set $E$ and $f : 2^E \to \mathbb Z_{\ge 0}$ → `Fin n` and `f : Finset (Fin n) → ℕ`, marginals and deficiencies computed in `ℤ`; reason: Lean convention; the same instances
--   - encoding: $k := (2d-1)\cdot\chi^\circ(f) - (2d-2)$ → a natural number `k` with `(k : ℤ) = (2d − 1)·χ°(f) − (2d − 2)`; reason: under the hypotheses ($h$ exists and has $f(h) > 0$) the right side is at least 1, so this is the same $k$
--   - encoding: $\chi^\circ(f)$, the maximum in (1) → `chiCirc f`, a `Finset.sup` of natural ceilings `⌈·⌉₊` over the $T$ with $f(T) > 0$; reason: for a polymatroid every ratio in (1) is nonnegative and here the index set is nonempty ($f(E) \ge f(h) > 0$), so the sup is the max
--   - encoding: a valid $k$-coloring $S = S_1 \sqcup \dots \sqcup S_k$ → `col : Fin k → Finset (Fin n)` with pairwise disjoint independent classes whose union is $S$ (empty classes allowed); reason: the same partitions, with 0-based colors
-- source:
--   Bérczi, Chandrasekaran, Chekuri, Liu, Ravi, Approximate Covering and Packing in Polymatroids, STOC 2027 submission (manuscript sha256 47f38a6f…), Theorem 3.1, p.11 (PDF p.13)

import Mathlib
import Definitions.Def_PolymatroidCover_IsDPolymatroid
import Definitions.Def_PolymatroidCover_chiCirc
import Definitions.Def_PolymatroidCover_IsValidColoring

namespace PolymatroidCover

/-- Theorem 3.1 (Bérczi–Chandrasekaran–Chekuri–Liu–Ravi, *Approximate Covering and Packing in Polymatroids*, STOC 2027 submission (manuscript sha256 47f38a6f…), §3, printed p.11 = PDF p.13): let `f : 2^E → ℤ_{≥0}` be a
`d`-polymatroid and `k := (2d − 1)·χ°(f) − (2d − 2)`. For every `S ⊆ E` that admits a valid
`k`-coloring and every element `h ∈ E \ S`, the subset `S ∪ {h}` admits a valid `k`-coloring.

**Formalization Note** `E = Fin n`; `k` is a natural number with
`(k : ℤ) = (2d − 1)·χ°(f) − (2d − 2)`. The standing assumption of §2 (printed p.9), no
self-loops (`∀ e, 0 < f {e}`), is a binder: Theorem 3.1 is stated after it. -/
theorem theorem_3_1 {n : ℕ} (d k : ℕ) (f : Finset (Fin n) → ℕ) (hf : IsDPolymatroid d f)
    (hloop : ∀ e : Fin n, 0 < f {e})
    (hk : (k : ℤ) = (2 * (d : ℤ) - 1) * (chiCirc f : ℤ) - (2 * (d : ℤ) - 2))
    (S : Finset (Fin n)) (hS : ∃ col : Fin k → Finset (Fin n), IsValidColoring f S col)
    (h : Fin n) (hh : h ∉ S) :
    ∃ col' : Fin k → Finset (Fin n), IsValidColoring f (insert h S) col' := by sorry

end PolymatroidCover
