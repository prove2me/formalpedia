-- Prove2me | Theorems.Thm_ReconfRes_Frozen_frozenConnected_of_lift_frozenConnected
-- name    : ReconfRes.Frozen.frozenConnected_of_lift_frozenConnected
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-20T13:06:25.253317+00:00
-- url     : https://prove2.me/theorems/121a0922-0b07-4f2a-ad00-1bbab4159bd0
-- title:
--   Lemma 3.60 (1) — frozen paths between lifted tight refutations project to frozen paths of the inventory
-- statement:
--   Let $C_1,\dots,C_\alpha$ be an inventory of nonempty clauses (repetitions allowed), $w \ge 1 + \max_i |C_i|$, $k \ge 1$, and $t_1,\dots,t_\alpha$ distinct variables not occurring in any $C_j$. Put $D_i = C_i \cup \{\neg t_i\}$, $U_i = \{t_i\}$ and $H = \{D_i, U_i\}$. The lift of an indexed refutation $(R, \mathrm{pos})$ replaces the axiom node $\mathrm{pos}(i)$, labelled $C_i$, by the resolution on $t_i$ of two new axiom nodes labelled $D_i$ and $U_i$. If the lifts of two tight indexed refutations $R_1$, $R_2$ (lean refutations of the inventory's formula of size at most $2\alpha-1$, with the axiom nodes indexed by $1,\dots,\alpha$) lie in one connected component of the frozen graph $G^{\mathrm{fr}}_k(H, w, 4\alpha-1)$, then $R_1$ and $R_2$ lie in one connected component of $G^{\mathrm{fr}}_k(\text{inventory formula}, w, 2\alpha-1)$.
--
--   This is the first of the three clauses of Lemma 3.60 (private tags) in the formalization of Myrisiotis, *Reconfiguring Resolution Refutations*, STOC 2027 submission, §3.13, p. 78, stated as its own theorem; the other two clauses are `ReconfRes.Frozen.lemma_3_60`'s proved reduction. "Connected" is `FrozenConnected` (refutations up to renaming of nodes), the lift is `lift`, tightness is `IsTightIndexed`.
-- source:
--   Myrisiotis, Reconfiguring Resolution Refutations, STOC 2027 submission 340, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/340.pdf (no DOI), §3.13, p. 78, Lemma 3.60 (private tags), clause (1)

import Mathlib
import Definitions.Def_MultiplierAssoc206_Resolution_CNF
import Definitions.Def_ReconfRes_Frozen_Refutation
import Definitions.Def_ReconfRes_Frozen_FrozenGraph
import Definitions.Def_ReconfRes_Frozen_PrivateTags

open MultiplierAssoc206.Resolution
namespace ReconfRes.Frozen
theorem frozenConnected_of_lift_frozenConnected {V : Type} [DecidableEq V] (α : ℕ)
    (C : Fin α → Clause V) (hC : ∀ i, (C i).Nonempty) (w : ℕ)
    (hw : 1 + Finset.univ.sup (fun i => (C i).card) ≤ w)
    (t : Fin α → V) (ht : Function.Injective t) (hfresh : ∀ i j, ∀ l ∈ C j, l.1 ≠ t i)
    (k : ℕ) (hk : 1 ≤ k)
    (R₁ R₂ : ProofDag V) (pos₁ : Fin α → Fin R₁.n) (pos₂ : Fin α → Fin R₂.n)
    (h₁ : IsTightIndexed C R₁ pos₁) (h₂ : IsTightIndexed C R₂ pos₂)
    (hconn : FrozenConnected k (tagFormula C t) w (4 * α - 1) (lift C t R₁ pos₁) (lift C t R₂ pos₂)) :
    FrozenConnected k (inventoryFormula C) w (2 * α - 1) R₁ R₂ := by sorry
end ReconfRes.Frozen
