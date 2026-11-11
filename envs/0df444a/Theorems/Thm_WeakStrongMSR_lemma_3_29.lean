-- Prove2me | Theorems.Thm_WeakStrongMSR_lemma_3_29
-- name    : WeakStrongMSR.lemma_3_29
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T08:27:26.546957+00:00
-- url     : https://prove2.me/theorems/92085915-68e6-446d-8860-341a7b38b3b8
-- title:
--   Lemma 3.29 — with a strict majority of good witnesses, $d(c_J,x)\le\mathrm{md}(x,J)\le d(c_J,x)+2R_J$
-- statement:
--   Let $d$ be a metric, $C$ a corruption set and $\tilde d$ the weak distances for some adversary. Let $c_J$ be a point, $R_J$ a real, $B'$ a set of points within distance $R_J$ of $c_J$, $W$ a set of witnesses and $x$ a point. A witness $w\in W$ is **good** for $x$ if $w\in B'$ and the pair $\{x,w\}$ is not corrupted. Suppose strictly more than half of $W$ are good for $x$, and let
--   $$\mathrm{md}(x,J)=\operatorname{median}_{w\in W}\big(\tilde d(x,w)+d(c_J,w)\big).$$
--   Then:
--   1. $d(c_J,x)\le \mathrm{md}(x,J)\le d(c_J,x)+2R_J$;
--   2. if $x\in B'$, then $\mathrm{md}(x,J)\le 3R_J$, so the recomputed list contains $x$;
--   3. if $\mathrm{md}(x,J)\le 3R_J$, then $d(c_J,x)\le 3R_J$.
--
--   This is the correctness of the repaired lists.
--
--   **Formalization Note** The median is the lower median.
--
--   Differences from the source:
--   - generalization: B′_J = ⋃_{i∈J} B(s_i, 5R_i), with B′_J ⊆ B(c_J, R_J) by Lemma 3.19; W_J of size h → any set B′ inside B(c_J, R_J) and any witness set W; reason: covers B′_J and W_J
--   - reading: the median of h (even) values → the lower median; reason: the paper does not fix the middle value; a strict majority in an interval puts it there
-- source:
--   Friggstad–Jamshidian–Vakilian, Minimum Sum-of-Radii Clustering with Strong and Weak Oracles (manuscript, STOC 2027 submission, sha256 5f8fbaf3…67e8f92a0), Lemma 3.29, p.24 (PDF 25); Definition 3.27, p.24

import Mathlib
import Definitions.Def_MinSumClust_IsMetric
import Definitions.Def_MinSumRadiiPTAS_Main_Basic
import Definitions.Def_WeakStrongMSR_Model
import Definitions.Def_WeakStrongMSR_Estimates

open scoped Classical

set_option autoImplicit false

namespace WeakStrongMSR

/-- **Lemma 3.29** (Friggstad–Jamshidian–Vakilian, *Minimum Sum-of-Radii Clustering with Strong and Weak Oracles*
(manuscript, sha256 5f8fbaf3…67e8f92a0), p.24, PDF p.25; Definition 3.27, p.24).
"If more than half the witnesses of a large component J are good for an unqueried point x, then
d(c_J, x) ≤ md(x, J) ≤ d(c_J, x) + 2R_J. Consequently, x ∈ B′_J implies that the recomputed X_J
contains x, and membership in that recomputed list implies x ∈ B(c_J, 3R_J)." A witness `w ∈ W_J`
is good for `x` if `w ∈ B′_J` and the edge `xw` is honest.

Let `d` be a metric, `C` a corruption set, `adv` an adversary, `w = weakDist d C adv`, `c_J` a
point, `R_J` a real, `B′` a set of points within `R_J` of `c_J` (Lemma 3.19: `B′_J ⊆ B(c_J, R_J)`),
`W` a set of witnesses and `x` a point such that more than half of `W` are good for `x` (in `B′`,
with `{x, v} ∉ C`). With `md(x, J)` the lower median of `w(x, v) + d(c_J, v)` over `v ∈ W` (14):
1. `d(c_J, x) ≤ md(x, J) ≤ d(c_J, x) + 2R_J`;
2. if `x ∈ B′`, then `md(x, J) ≤ 3R_J` (`x` is in the recomputed list);
3. if `md(x, J) ≤ 3R_J`, then `d(c_J, x) ≤ 3R_J`.

**Formalization Note.** `B′` may be any set inside `B(c_J, R_J)` (this contains `B′_J` by Lemma
3.19); the witness set may have any size. -/
theorem lemma_3_29 {n : ℕ} (d : Fin n → Fin n → ℝ) (hd : MinSumClust.IsMetric d)
    (C : Finset (Sym2 (Fin n))) (adv : Adversary n) (cJ : Fin n) (RJ : ℝ)
    (B' W : Finset (Fin n)) (hB' : ∀ y ∈ B', d cJ y ≤ RJ) (x : Fin n)
    (hgood : W.card < 2 * (W.filter (fun v => v ∈ B' ∧ s(x, v) ∉ C)).card) :
    (d cJ x ≤ mdComp d (weakDist d C adv) cJ W x ∧
      mdComp d (weakDist d C adv) cJ W x ≤ d cJ x + 2 * RJ) ∧
    (x ∈ B' → mdComp d (weakDist d C adv) cJ W x ≤ 3 * RJ) ∧
    (mdComp d (weakDist d C adv) cJ W x ≤ 3 * RJ → d cJ x ≤ 3 * RJ) := by sorry

end WeakStrongMSR
