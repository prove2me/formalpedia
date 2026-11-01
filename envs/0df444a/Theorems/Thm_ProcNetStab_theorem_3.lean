-- Prove2me | Theorems.Thm_ProcNetStab_theorem_3
-- name    : ProcNetStab.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T12:43:35.794221+00:00
-- url     : https://prove2.me/theorems/6d4e44d1-d863-4282-80a7-a6a862f96fa0
-- title:
--   Theorem 3 (Chambers–Echenique, Thm 1.5): an order pair has a weak-order extension iff it is acyclic
-- statement:
--   Let $X$ be a set and $\langle R, P\rangle$ an order pair on $X$, that is, binary relations with $P \subseteq R$. There is a preference relation (weak order) $\succeq$ on $X$ such that $\langle \succeq, \succ\rangle$ is an order pair extension of $\langle R, P\rangle$,
--   $$
--   R \subseteq {\succeq} \qquad\text{and}\qquad P \subseteq {\succ},
--   $$
--   if and only if $\langle R, P\rangle$ is acyclic.
--
--   The paper uses this result to turn acyclic revealed preference relations over networks into complete and transitive preferences.
--
--   Differences from the source:
--
--   - generalization: order pairs on the finite set G of networks → order pairs on an arbitrary type X; reason: the paper applies Theorem 3 (stated by Chambers and Echenique for arbitrary sets) to G; the finite set is an instance
--   - encoding: no sequence x₁ R x₂ R … R x_L with x_L P x₁ → ∀ x y, ReflTransGen R x y → ¬ P y x; reason: Lean convention for chains of length L ≥ 1; same instances
-- source:
--   Chiong, Qi, Stability of Procurement Networks (authors' manuscript, 2025), Theorem 3, p.OA-4 (PDF p.33), citing Theorem 1.5 of Chambers and Echenique (2016)

import Mathlib
import Definitions.Def_ProcNetStab_IsAcyclic

namespace ProcNetStab

/-- **Theorem 3 (Theorem 1.5 of Chambers and Echenique (2016))** (Chiong, Qi, *Stability of
Procurement Networks* (authors' manuscript, 2025), Theorem 3, p.OA-4 (PDF p.33)): let `⟨R, P⟩` be
an order pair (`P ⊆ R`). There is a preference relation `⪰` such that `⟨⪰, ≻⟩` is an order pair
extension of `⟨R, P⟩` if and only if `⟨R, P⟩` is acyclic.

**Formalization Note** The set `X` is an arbitrary type (the paper applies the theorem to the
finite set of networks `G`). -/
theorem theorem_3 {X : Type*} (R P : X → X → Prop) (hPR : ∀ x y, P x y → R x y) :
    (∃ W : X → X → Prop, IsWeakOrder W ∧ IsOrderPairExtension W R P) ↔ IsAcyclic R P := by sorry

end ProcNetStab
