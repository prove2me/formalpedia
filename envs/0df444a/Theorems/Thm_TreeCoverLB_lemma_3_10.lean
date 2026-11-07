-- Prove2me | Theorems.Thm_TreeCoverLB_lemma_3_10
-- name    : TreeCoverLB.lemma_3_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:24:31.977868+00:00
-- url     : https://prove2.me/theorems/3e00726f-6cec-43c6-8336-45843d1760c6
-- title:
--   Lemma 3.10: no map $C(E_dG,v)\to|E_dG|$ equivariant on the base
-- statement:
--   Let $G$ be a nontrivial finite group and $d\ge 0$. There is no continuous map from the cone
--   $$
--   C(E_dG)=\{tx: 0\le t\le 1,\ x\in|E_dG|\}
--   $$
--   to $|E_dG|$ whose restriction to the base $|E_dG|$ is $G$-equivariant.
--
--   This is the form of Dold's theorem used in §4: the labels of a tree cover would produce exactly such a map.
--
--   Differences from the source:
--   - encoding: the cone C(E_dG, v) = |E_dG ∗ ∆{v}| ⊆ ℝ^{V∪{v}} → {t x : 0 ≤ t ≤ 1, x ∈ |E_dG|} ⊆ ℝ^V; reason: the paper's own identification (Definition 3.5), a linear homeomorphism fixing the base
--   - encoding: a continuous map C(E_dG, v) → |E_dG| → a function continuous on the cone and mapping it into |E_dG|, equivariant at every base point and every g; reason: only the values on the cone matter; G written additively
-- source:
--   Chen, Huang, Tan, Xu, Improved Lower Bounds on Tree Covers, arXiv:2607.27264 (version of October 31, 2026), Lemma 3.10, p.10 (PDF p.12); equivalence with Theorem 3.9 in Appendix A, p.35

import Mathlib
import Definitions.Def_TreeCoverLB_realization
import Definitions.Def_TreeCoverLB_EJoin
import Definitions.Def_TreeCoverLB_scaledCone

open Classical

namespace TreeCoverLB

/-- **Lemma 3.10** (Chen, Huang, Tan, Xu, *Improved Lower Bounds on Tree Covers*, arXiv:2607.27264 (version of October 31, 2026), Lemma 3.10, p.10 (PDF p.12)): let `G` be a nontrivial finite group and
`d ≥ 0`. There is no continuous map `C(E_dG, v) → |E_dG|` whose restriction to the base `|E_dG|` is
`G`-equivariant.

**Formalization Note** The cone `C(E_dG, v)` is identified, as in Definition 3.5 of the paper, with
`C(E_dG) = {t x : 0 ≤ t ≤ 1, x ∈ |E_dG|} ⊆ ℝ^{[d+1] × G}` (`scaledCone _ 1`): the apex is the origin
and the base is `|E_dG|` itself. `F` is continuous on the cone, maps it into `|E_dG|`, and is
equivariant on the base only, for every `g`. The group is written additively. -/
theorem lemma_3_10 {G : Type*} [AddGroup G] [Fintype G] [Nontrivial G] (d : ℕ) :
    ¬ ∃ F : (Fin (d + 1) × G → ℝ) → (Fin (d + 1) × G → ℝ),
      ContinuousOn F (scaledCone (EJoin d G) 1) ∧
      Set.MapsTo F (scaledCone (EJoin d G) 1) (realization (EJoin d G)) ∧
      ∀ g : G, ∀ μ ∈ realization (EJoin d G), F (ejoinAct g μ) = ejoinAct g (F μ) := by sorry

end TreeCoverLB
