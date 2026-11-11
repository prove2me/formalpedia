-- Prove2me | Theorems.Thm_ProdMomentConc_lemma_A_1
-- name    : ProdMomentConc.lemma_A_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:13:28.772109+00:00
-- url     : https://prove2.me/theorems/4d809674-a6d9-4ea8-bc70-789a94674db8
-- title:
--   Lemma A.1 — Janson's fractional-cover Hoeffding bound under negative association
-- statement:
--   Let $V$ be a finite set and $(Z_x)_{x \in V}$ random variables with values in $[0,1]$; set $Z := \sum_{x \in V} Z_x$. Let $\{(V_j, w_j)\}_j$ be a **fractional cover** of $V$: $V_j \subseteq V$, $w_j \ge 0$, and
--
--   $$
--   \sum_{j : x \in V_j} w_j \ge 1 \quad \text{for every } x \in V.
--   $$
--
--   Assume that for each $j$ the variables $(Z_x)_{x \in V_j}$ are negatively associated, and let $W := \sum_j w_j$. Then for every $t > 0$,
--
--   $$
--   \Pr[Z \ge \mathbb E Z + t] \le \exp\Big(-\frac{2t^2}{W|V|}\Big).
--   $$
--
--   This is Janson's fractional-cover version of Hoeffding's inequality, with independence inside each cover class weakened to negative association. Taking the infimum of $W$ over covers by stable sets of a dependency graph gives a bound in terms of its fractional chromatic number, as in (13).
--
--   **Formalization Note** $V$ is a finite type and the cover is a finite family $(V_j, w_j)_{j \in \iota}$ indexed by a finite type (classes may repeat). The $Z_x$ are measurable. Negative association is `IsNegAssoc`.
--
--   Differences from the source:
--   - encoding: a fractional cover {(V_j, w_j)}_j with no stated index set → a family indexed by a finite type; reason: V has finitely many subsets, so a cover with finite total weight can be merged into a finite one with the same W, and for W = ∞ the bound is trivial
-- source:
--   Saks, Srinivasan, Valieva, Concentration from Product Moments via an Additional Element of Randomness, arXiv:2608.04125 (held version, sha256 5218e9d0405f975413d3e2dd2c4c9d6b43c772029e645965afee1cd619ae38aa), Lemma A.1, p.33 (PDF p.33), after [Jan04]

import Mathlib
import Definitions.Def_ProdMomentConc_IsNegAssoc

open MeasureTheory ProbabilityTheory

namespace ProdMomentConc

/-- **Lemma A.1 (Janson's fractional-cover bound under negative association).**
Saks, Srinivasan, Valieva, *Concentration from Product Moments via an Additional Element of
Randomness*, arXiv:2608.04125 (held version, sha256 5218e9d0…), Lemma A.1, p.33.

Let `(Z_x)_{x∈V}` be random variables with values in `[0, 1]` and `Z := ∑_{x∈V} Z_x`. Let
`{(V_j, w_j)}_j` be a fractional cover of `V`: `V_j ⊆ V`, `w_j ≥ 0`, and `∑_{j : x ∈ V_j} w_j ≥ 1`
for every `x ∈ V`. Assume that for each `j` the variables `(Z_x)_{x∈V_j}` are negatively
associated, and let `W := ∑_j w_j`. Then for every `t > 0`,
`Pr[Z ≥ EZ + t] ≤ exp(−2t²/(W|V|))`.

**Formalization Note.** `V` is a finite type and the cover is a finite family indexed by a finite
type `ι` (the classes `Vc j` need not be distinct); since `V` has finitely many subsets, a family
with finite total weight can always be merged into such a finite one with the same `W`. The
`Z_x` are measurable (random variables). Negative association is `IsNegAssoc` (Definition 2.10). -/
theorem lemma_A_1 {Ω V ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    [Fintype V] [DecidableEq V] [Fintype ι]
    (Z : V → Ω → ℝ) (hZm : ∀ x, Measurable (Z x)) (hZ : ∀ x ω, 0 ≤ Z x ω ∧ Z x ω ≤ 1)
    (Vc : ι → Finset V) (w : ι → ℝ) (hw : ∀ j, 0 ≤ w j)
    (hcover : ∀ x, 1 ≤ ∑ j ∈ Finset.univ.filter (fun j => x ∈ Vc j), w j)
    (hNA : ∀ j, IsNegAssoc (fun x : Vc j => Z x) μ) (t : ℝ) (ht : 0 < t) :
    μ.real {ω | (∫ ω', ∑ x, Z x ω' ∂μ) + t ≤ ∑ x, Z x ω} ≤
      Real.exp (-(2 * t ^ 2 / ((∑ j, w j) * (Fintype.card V : ℝ)))) := by sorry

end ProdMomentConc
