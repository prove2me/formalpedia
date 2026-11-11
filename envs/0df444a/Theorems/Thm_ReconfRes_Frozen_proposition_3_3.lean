-- Prove2me | Theorems.Thm_ReconfRes_Frozen_proposition_3_3
-- name    : ReconfRes.Frozen.proposition_3_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T19:23:13.446795+00:00
-- url     : https://prove2.me/theorems/daf7122c-b82f-400b-b562-c16fb36d42b1
-- title:
--   Proposition 3.3 — frozen moves preserve the multiset of axiom clauses; different multisets lie in different components
-- statement:
--   Let $F$ be a CNF formula, $k\ge1$ a locality, $w$ a width bound and $s$ a size budget. If $R$ and $R'$ are adjacent in the frozen lean graph $G^{fr}_k(F,w,s)$, they have the same multiset of axiom clauses, counted with multiplicity over axiom nodes. Consequently two vertices whose axiom multisets differ lie in different connected components:
--   $$R\sim R'\ \Rightarrow\ \mathrm{Ax}(R)=\mathrm{Ax}(R'),\qquad \mathrm{Ax}(R)\ne\mathrm{Ax}(R')\ \Rightarrow\ R\not\leftrightsquigarrow R'.$$
--   This is the invariant that splits the frozen graph by axiom inventory, so that reachability is a question inside one inventory.
--
--   Differences from the source:
--   - encoding: refutations identified up to renaming of nodes (p. 19, p. 23) → concrete DAGs on Fin n; adjacency is invariant under renaming and connectivity steps include isomorphisms; reason: Lean needs concrete presentations; the components are those of the graph on isomorphism classes
-- source:
--   Myrisiotis, Reconfiguring Resolution Refutations, STOC 2027 submission (manuscript sha256 8b5124c1…), p. 22, Proposition 3.3

import Mathlib
import Definitions.Def_MultiplierAssoc206_Resolution_CNF
import Definitions.Def_ReconfRes_Frozen_Refutation
import Definitions.Def_ReconfRes_Frozen_FrozenGraph

open MultiplierAssoc206.Resolution

namespace ReconfRes.Frozen

/-- **Proposition 3.3** (frozen moves preserve the axiom nodes). Adjacent vertices of
`G^fr_k(F,w,s)` have the same multiset of axiom clauses; consequently two vertices whose axiom
multisets differ lie in different connected components. -/
theorem proposition_3_3 {V : Type} [DecidableEq V] (k : ℕ) (hk : 1 ≤ k) (F : CNF V) (w s : ℕ) :
    (∀ R R' : ProofDag V, FrozenAdj k F w s R R' → R.axiomMultiset = R'.axiomMultiset) ∧
    (∀ R R' : ProofDag V, IsVertex F w s R → IsVertex F w s R' →
      R.axiomMultiset ≠ R'.axiomMultiset → ¬ FrozenConnected k F w s R R') := by sorry

end ReconfRes.Frozen
