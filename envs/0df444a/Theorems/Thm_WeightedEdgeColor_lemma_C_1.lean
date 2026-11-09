-- Prove2me | Theorems.Thm_WeightedEdgeColor_lemma_C_1
-- name    : WeightedEdgeColor.lemma_C_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T02:49:41.89912+00:00
-- url     : https://prove2.me/theorems/6711e5e7-efb9-4c1e-8ab9-5ede2feb9d42
-- title:
--   Lemma C.1 — bounded-profile compression of a local feasible-set distribution
-- statement:
--   Consider one finite set of items with weights $w_e\in(0,1]$. Fix a small $\beta>0$; an item is **large** if $w_e\ge\beta$ and **small** otherwise, and $K=\lfloor1/\beta\rfloor$. A **profile** consists of slots of sizes $b_1,\dots,b_K\ge0$ (zero sizes allowed) and a reserved space $R\ge0$ for small items; it is **valid** if $\sum_ib_i+R\le1$.
--
--   Fix $0<\delta<1$ and $0<\beta\le r_0=\delta/4$. There is $M=M(\beta,\delta)$, depending only on $\beta$ and $\delta$, with the following property. For every finite item set and every $x\in\mathcal K$ (an average of feasible sets), there are at most $M$ valid profiles $P$, probabilities $\lambda_P\ge0$ with $\sum_P\lambda_P=1$, and nonnegative assigned fractions $a(e;P,i)$ (for slots $i$) and $a(e;P,R)$ (for the reserved space) such that, with $y_e=(1-\delta)x_e$,
--   $$
--   \sum_{P,i}a(e;P,i)=y_e,\tag{C.1}
--   $$
--   $$
--   \sum_e a(e;P,i)\le\lambda_P\quad\text{for each large-item slot } i,\tag{C.2}
--   $$
--   $$
--   \sum_{e:\,w_e<\beta}w_e\,a(e;P,R)\le\lambda_P R\quad\text{for the reserved space},\tag{C.3}
--   $$
--   where the sum in (C.1) runs over all slots and the reserved space. Moreover:
--   1. large items are assigned only to slots that can hold their weight ($w_e\le b_i$);
--   2. small items are assigned only to positive reserved spaces, and every positive reserved space has size at least $r_0$;
--   3. every individual assigned fraction is at most $y_e$.
--
--   The lemma replaces an arbitrary local distribution over feasible bins, whose number of distinct bins may grow with the input, by a bounded menu of profiles at the cost of a $\delta$ fraction of each inclusion probability.
--
--   **Formalization Note** The profiles are indexed by $\{1,\dots,M\}$; profiles of probability zero and repeated profiles are allowed. The assignment to slots and to the reserved space are two separate families of numbers.
--
--   Differences from the source:
--   - encoding: at most $M$ valid profiles → a family of exactly $M$ profiles, repetitions and zero probabilities allowed; reason: unused indices get probability and fractions zero, and repeated profiles can be merged, so the two forms are equivalent
--   - reading: "positive reserved spaces, each of which has size at least $r_0$" → every profile's reserved space is $0$ or at least $r_0$; reason: the stronger of the two readings (the proof rounds every reserved space to a multiple of $r_0$)
--   - reading: items with weights $w_e\le1$ (§C.1) → weights in $(0,1]$; reason: the items are the edges at one vertex, whose weights lie in $(0,1]$ by the standing convention of Appendix A (p.24)
-- source:
--   Gajjala, Khan, Asymptotically Optimal Weighted Edge Colorings via Local Bin Packing, preprint (arXiv:2611.03190, version not stamped), Lemma C.1, p.34; setting §C.1, p.33

import Mathlib
import Definitions.Def_WeightedEdgeColor_IsAvgOfFeasibleSets

set_option autoImplicit false

namespace WeightedEdgeColor

/-- Lemma C.1 (bounded-profile compression).

Source: Gajjala, Khan, preprint of November 2, 2026 (arXiv:2611.03190, version not stamped),
Lemma C.1, p.34 (setting §C.1, p.33).

**Formalization Note.** One finite set of items `ι` with weights in `(0, 1]`; an item is large
if `w_e ≥ β` and small otherwise; `K = ⌊1/β⌋`. A profile `P : Fin M` has slot sizes
`b P i` (`i : Fin K`, zero sizes allowed) and reserved space `R P`; it is valid if all are
nonnegative and `∑_i b P i + R P ≤ 1`. "At most `M` profiles" is a family indexed by `Fin M`
(profiles of probability zero and repetitions allowed). `aL e P i` is `a(e; P, i)` for a slot
`i` and `aS e P` is `a(e; P, R)`. The bound `M` depends only on `β` and `δ` (chosen before the
items). "Every positive reserved space has size at least `r₀ = δ/4`" is asserted for every
profile. -/
theorem lemma_C_1 (δ β : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hβ0 : 0 < β) (hβ : β ≤ δ / 4) :
    ∃ M : ℕ, ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (w x : ι → ℝ),
      (∀ e, 0 < w e) → (∀ e, w e ≤ 1) → IsAvgOfFeasibleSets w x →
      ∃ (lam : Fin M → ℝ) (b : Fin M → Fin ⌊1 / β⌋₊ → ℝ) (R : Fin M → ℝ)
        (aL : ι → Fin M → Fin ⌊1 / β⌋₊ → ℝ) (aS : ι → Fin M → ℝ),
        -- valid profiles
        (∀ P, (∀ i, 0 ≤ b P i) ∧ 0 ≤ R P ∧ ∑ i, b P i + R P ≤ 1) ∧
        -- probabilities
        (∀ P, 0 ≤ lam P) ∧ ∑ P, lam P = 1 ∧
        -- nonnegative assigned fractions
        (∀ e P i, 0 ≤ aL e P i) ∧ (∀ e P, 0 ≤ aS e P) ∧
        -- (C.1)
        (∀ e, ∑ P, (∑ i, aL e P i + aS e P) = (1 - δ) * x e) ∧
        -- (C.2)
        (∀ P i, ∑ e, aL e P i ≤ lam P) ∧
        -- (C.3)
        (∀ P, ∑ e ∈ Finset.univ.filter (fun e => w e < β), w e * aS e P ≤ lam P * R P) ∧
        -- large items only in slots that can hold their weight
        (∀ e P i, aL e P i ≠ 0 → β ≤ w e ∧ w e ≤ b P i) ∧
        -- small items only in positive reserved spaces
        (∀ e P, aS e P ≠ 0 → w e < β ∧ 0 < R P) ∧
        -- every positive reserved space has size at least r₀ = δ/4
        (∀ P, R P = 0 ∨ δ / 4 ≤ R P) ∧
        -- every individual assigned fraction is at most y_e = (1 - δ) x_e
        (∀ e P i, aL e P i ≤ (1 - δ) * x e) ∧ (∀ e P, aS e P ≤ (1 - δ) * x e) := by sorry

end WeightedEdgeColor
