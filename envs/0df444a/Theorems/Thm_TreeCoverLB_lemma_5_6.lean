-- Prove2me | Theorems.Thm_TreeCoverLB_lemma_5_6
-- name    : TreeCoverLB.lemma_5_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:25:04.00822+00:00
-- url     : https://prove2.me/theorems/34a65932-66a4-4530-90b7-8a211266c405
-- title:
--   Lemma 5.6: the strict region $U$ of $|\Delta_G|$ maps equivariantly to $|E_{k-3}G|$
-- statement:
--   Let $k\ge 3$, let $p\ge k-1$ be prime and $G=\mathbb Z_p$, acting on $|\Delta_G|\subseteq\mathbb R^G$ by $(s\cdot a)_g=a_{g-s}$. Let
--   $$
--   U=\Big\{a\in|\Delta_G|:\ \max_{g\in G}a_g>\frac1{k-1}\Big\}.
--   $$
--   Then $U$ is a $G$-invariant open subspace of $|\Delta_G|$, and there is a continuous $G$-equivariant map $U\to|E_{k-3}G|$.
--
--   Differences from the source:
--   - encoding: max_g a_g > 1/(k − 1); U open in |∆_G| → ∃ g, a_g > 1/(k − 1); the preimage of U in the subtype |∆_G| is open; reason: equivalent formulations
-- source:
--   Chen, Huang, Tan, Xu, Improved Lower Bounds on Tree Covers, arXiv:2607.27264 (version of October 31, 2026), Lemma 5.6, p.19 (PDF p.21); standing assumptions of §5, p.18 (PDF p.20)

import Mathlib
import Definitions.Def_TreeCoverLB_realization
import Definitions.Def_TreeCoverLB_EJoin
import Definitions.Def_TreeCoverLB_simplexAct

open Classical

namespace TreeCoverLB

/-- **Lemma 5.6** (Chen, Huang, Tan, Xu, *Improved Lower Bounds on Tree Covers*, arXiv:2607.27264 (version of October 31, 2026), Lemma 5.6, p.19 (PDF p.21); §5 standing assumptions p.18): let `k ≥ 3`,
let `p ≥ k − 1` be prime and `G = ℤ_p`, acting on `|∆_G| ⊆ ℝ^G` by `(s · a)_g = a_{g−s}`. Let
`U := {a ∈ |∆_G| : max_{g ∈ G} a_g > 1/(k − 1)}`. Then `U` is a `G`-invariant open subspace of
`|∆_G|`, and there is a continuous `G`-equivariant map `U → |E_{k−3}G|`.

**Formalization Note** `|∆_G|` is the realization of the full simplex (all finsets of `ZMod p`), the
standard simplex in `ℝ^G`. `max_g a_g > c` is `∃ g, a_g > c`. "Open subspace of `|∆_G|`" is openness
of the preimage of `U` in the subtype `|∆_G|`. The map is a function on `ℝ^G`, continuous on `U`,
mapping `U` into `|E_{k−3}G|` and equivariant for every `s` and every point of `U`. -/
theorem lemma_5_6 (k : ℕ) (hk : 3 ≤ k) (p : ℕ) [Fact p.Prime] (hp : k - 1 ≤ p)
    (U : Set (ZMod p → ℝ))
    (hU : U = {a | a ∈ realization (Set.univ : Set (Finset (ZMod p))) ∧
      ∃ g, 1 / ((k : ℝ) - 1) < a g}) :
    (∀ s : ZMod p, ∀ a ∈ U, simplexAct s a ∈ U) ∧
    IsOpen ((Subtype.val : realization (Set.univ : Set (Finset (ZMod p))) → (ZMod p → ℝ)) ⁻¹' U) ∧
    ∃ F : (ZMod p → ℝ) → (Fin (k - 3 + 1) × ZMod p → ℝ),
      ContinuousOn F U ∧ Set.MapsTo F U (realization (EJoin (k - 3) (ZMod p))) ∧
      ∀ s : ZMod p, ∀ a ∈ U, F (simplexAct s a) = ejoinAct s (F a) := by sorry

end TreeCoverLB
