-- Prove2me | Theorems.Thm_ReconfRes_Frozen_lemma_3_60
-- name    : ReconfRes.Frozen.lemma_3_60
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T19:24:26.631907+00:00
-- url     : https://prove2.me/theorems/8b45232a-d104-4d26-9155-386c308dd8f4
-- title:
--   Lemma 3.60 — private tags: frozen paths between tagged lifts project; consistently indexed frozen paths lift; H has 2α distinct clauses, Horn if the C_i are
-- statement:
--   Let $C_1,\dots,C_\alpha$ be a prescribed inventory of nonempty axiom occurrences, with repetitions allowed, and let $w\ge1+\max_i|C_i|$. Choose distinct fresh variables $t_i$ and put $D_i=C_i\cup\{\neg t_i\}$, $U_i=\{t_i\}$, $H=\{D_i,U_i:1\le i\le\alpha\}$. Lift a tight refutation with this inventory by replacing its $i$-th source with the resolution of $D_i,U_i$ on $t_i$. For every $k\ge1$:
--   1. every locality-$k$ frozen path between lifted endpoints over $H$, at width $w$ and size budget $4\alpha-1$, projects to a frozen path between the old endpoints at width $w$ and size budget $2\alpha-1$;
--   2. every old locality-$k$ frozen path at these latter bounds lifts to a path between its specified lifts, provided its source occurrences have consistent indices throughout the path, including at both endpoints.
--
--   Both paths use locality at most $k$. The $2\alpha$ clauses of $H$ are distinct, and $H$ is Horn if every $C_i$ is Horn:
--   $$|H|=2\alpha .$$
--   Applied twice, it turns a prescribed-inventory instance into a one-copy instance (Corollary 3.64).
--
--   Differences from the source:
--   - reading: "fresh" variables; the old proofs' formula → t injective with no t_i occurring in any C_j; the old graph is over the formula {C_1, …, C_α} (the set of inventory clauses); reason: the lemma names no other formula; the old proofs are refutations with this inventory
--   - encoding: the inventory C_1, …, C_α and the i-th source → C : Fin α → clauses; tight indexed refutations (R, pos) with pos i the node of C_i; reason: indices are exactly what statement (2) is about
--   - encoding: budgets 2α − 1, 4α − 1, size at most 2α − 1 → natural-number expressions 2α − 1, 4α − 1 in the graph, and |R| + 1 ≤ 2α for tightness; reason: they agree for α ≥ 1; for α = 0 no refutation exists either way
-- source:
--   Myrisiotis, Reconfiguring Resolution Refutations, STOC 2027 submission (manuscript sha256 8b5124c1…), pp. 78–79, Lemma 3.60

import Mathlib
import Definitions.Def_MultiplierAssoc206_Resolution_CNF
import Definitions.Def_ReconfRes_Frozen_Refutation
import Definitions.Def_ReconfRes_Frozen_FrozenGraph
import Definitions.Def_ReconfRes_Frozen_PrivateTags

open MultiplierAssoc206.Resolution

namespace ReconfRes.Frozen

/-- **Lemma 3.60** (private tags). Let `C₁, …, C_α` be an inventory of nonempty clauses
(repetitions allowed), `w ≥ 1 + maxᵢ |Cᵢ|`, and `t₁, …, t_α` distinct variables not occurring in
any `Cⱼ`; put `Dᵢ = Cᵢ ∪ {¬tᵢ}`, `Uᵢ = {tᵢ}`, `H = {Dᵢ, Uᵢ}`. For every `k ≥ 1`:
(1) if the lifts of two tight indexed refutations are joined by a locality-`k` frozen path over `H`
at width `w` and size budget `4α − 1`, the refutations themselves are joined by a locality-`k`
frozen path over the inventory's formula at width `w` and size budget `2α − 1`;
(2) a locality-`k` frozen path at width `w` and budget `2α − 1` that keeps the indices of the
source occurrences (moves and identifications preserve them) lifts to a path between the lifts of
its indexed endpoints;
(3) the `2α` clauses of `H` are distinct, and `H` is Horn if every `Cᵢ` is Horn. -/
theorem lemma_3_60 {V : Type} [DecidableEq V] (α : ℕ) (C : Fin α → Clause V)
    (hC : ∀ i, (C i).Nonempty) (w : ℕ) (hw : 1 + Finset.univ.sup (fun i => (C i).card) ≤ w)
    (t : Fin α → V) (ht : Function.Injective t) (hfresh : ∀ i j, ∀ l ∈ C j, l.1 ≠ t i)
    (k : ℕ) (hk : 1 ≤ k) :
    (∀ (R₁ R₂ : ProofDag V) (pos₁ : Fin α → Fin R₁.n) (pos₂ : Fin α → Fin R₂.n),
      IsTightIndexed C R₁ pos₁ → IsTightIndexed C R₂ pos₂ →
      FrozenConnected k (tagFormula C t) w (4 * α - 1) (lift C t R₁ pos₁) (lift C t R₂ pos₂) →
      FrozenConnected k (inventoryFormula C) w (2 * α - 1) R₁ R₂) ∧
    (∀ (R₁ R₂ : ProofDag V) (pos₁ : Fin α → Fin R₁.n) (pos₂ : Fin α → Fin R₂.n),
      IndexedFrozenConnected k (inventoryFormula C) w (2 * α - 1) C Finset.univ ⟨R₁, pos₁⟩ ⟨R₂, pos₂⟩ →
      FrozenConnected k (tagFormula C t) w (4 * α - 1) (lift C t R₁ pos₁) (lift C t R₂ pos₂)) ∧
    (tagFormula C t).card = 2 * α ∧
    ((∀ i, IsHornClause (C i)) → IsHorn (tagFormula C t)) := by sorry

end ReconfRes.Frozen
