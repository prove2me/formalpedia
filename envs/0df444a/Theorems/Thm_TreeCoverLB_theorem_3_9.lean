-- Prove2me | Theorems.Thm_TreeCoverLB_theorem_3_9
-- name    : TreeCoverLB.theorem_3_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:24:30.716245+00:00
-- url     : https://prove2.me/theorems/af77045a-d4e4-48b5-86b5-dc6a74d0a1b2
-- title:
--   Theorem 3.9 (Dold): no equivariant map $|E_{d+1}G|\to|E_dG|$
-- statement:
--   **Dold's theorem.** Let $G$ be a nontrivial finite group and $d\ge 0$. There is no continuous $G$-equivariant map
--   $$
--   |E_{d+1}G|\longrightarrow|E_dG|,
--   $$
--   where $G$ acts on both joins layerwise.
--
--   This Borsuk–Ulam-type obstruction is the topological input of the lower bound, used through Lemma 3.10.
--
--   Differences from the source:
--   - encoding: a continuous map |E_{d+1}G| → |E_dG| → a function on ℝ^{[d+2]×G} that is continuous on |E_{d+1}G| and maps it into |E_dG|; reason: only the values on |E_{d+1}G| matter; the same maps
--   - encoding: a finite group G written multiplicatively → an additive (not necessarily commutative) group; reason: notation only
-- source:
--   Chen, Huang, Tan, Xu, Improved Lower Bounds on Tree Covers, arXiv:2607.27264 (version of October 31, 2026), Theorem 3.9, p.10 (PDF p.12); cited from [Dol83] and [Mat03, Theorem 6.2.5]

import Mathlib
import Definitions.Def_TreeCoverLB_realization
import Definitions.Def_TreeCoverLB_EJoin

open Classical

namespace TreeCoverLB

/-- **Theorem 3.9 (Dold's theorem)** (Chen, Huang, Tan, Xu, *Improved Lower Bounds on Tree Covers*, arXiv:2607.27264 (version of October 31, 2026), Theorem 3.9, p.10 (PDF p.12); cited from [Dol83],
[Mat03, Theorem 6.2.5]): if `G` is a nontrivial finite group and `d ≥ 0`, there is no continuous
`G`-equivariant map `|E_{d+1}G| → |E_dG|`.

**Formalization Note** The group is written additively (`AddGroup`, not necessarily commutative)
and acts on both joins layerwise, `g · (i, h) = (i, g + h)` (`ejoinAct`). A map `|E_{d+1}G| → |E_dG|`
is a function `F` on the ambient space `ℝ^{[d+2] × G}` that is continuous on `|E_{d+1}G|`
(subspace topology) and maps it into `|E_dG|`; equivariance is required for every `g` and every
point of `|E_{d+1}G|`. -/
theorem theorem_3_9 {G : Type*} [AddGroup G] [Fintype G] [Nontrivial G] (d : ℕ) :
    ¬ ∃ F : (Fin (d + 1 + 1) × G → ℝ) → (Fin (d + 1) × G → ℝ),
      ContinuousOn F (realization (EJoin (d + 1) G)) ∧
      Set.MapsTo F (realization (EJoin (d + 1) G)) (realization (EJoin d G)) ∧
      ∀ g : G, ∀ μ ∈ realization (EJoin (d + 1) G), F (ejoinAct g μ) = ejoinAct g (F μ) := by sorry

end TreeCoverLB
