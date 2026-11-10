-- Prove2me | Theorems.Thm_UniformSubpower_Supplied_lemma_8_2
-- name    : UniformSubpower.Supplied.lemma_8_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T05:20:38.981895+00:00
-- url     : https://prove2.me/theorems/0a909ed0-e6ad-4289-9ef7-01e72d187881
-- title:
--   Lemma 8.2 — one subgroup for all occupied fibres
-- statement:
--   In the sparse central setting of §8 ($M$ physical rows $A_v = L_v \times Q_v$ with finite abelian groups $L_v$, checked sparse operations of the affine form (16), a rowwise Mal'tsev operation $m$ with coefficients $(\mathrm{id}, -\mathrm{id}, \mathrm{id})$, a nonempty input set $H$ and $T = \mathrm{Sg}(H)$), there is a subgroup $H_T \le \prod_v L_v$ such that each occupied fibre of $T$ is an affine coset of $H_T$:
--   $$\{x \in T : \pi(x) = \pi(t)\} = t + H_T \qquad \text{for every } t \in T .$$
--
--   It says that a single subgroup describes the central part of every quotient fibre of the generated relation, which is what lets the central engine represent $T$ by its quotient relation plus one group.
--
--   **Formalization Note.** `CentralSetting` carries the data of §8; `S.translate t d` is the central translation $t + d$.
--
--   Differences from the source:
--   - encoding: input tuple list H ≠ ∅, checked sparse operations and m given by small tables verified to have the affine forms (16), (17) → a nonempty set H and operations given by their affine data; reason: a table of the affine form is exactly such data, and a subset of a finite product is finite.
-- source:
--   Gkantzounis, Uniform Subpower Membership for Finite Mal'tsev Algebras, STOC 2027 submission (manuscript sha256 149e66b1…), p. 23, Lemma 8.2

import Mathlib
import Definitions.Def_UniformSubpower_Supplied_SparseCentral

namespace UniformSubpower.Supplied

/-- Lemma 8.2 (Gkantzounis, p. 23): one subgroup for all occupied fibres. In the sparse central
setting of §8 there is a subgroup `H_T ≤ ∏_v L_v` such that every occupied fibre
`{x ∈ T : π(x) = π(t)}` (`t ∈ T`) is the coset `t + H_T`. -/
theorem lemma_8_2 {M : ℕ} {L Q : Fin M → Type} [∀ v, AddCommGroup (L v)]
    [∀ v, Fintype (L v)] [∀ v, Fintype (Q v)] (S : CentralSetting M L Q) :
    ∃ HT : AddSubgroup ((v : Fin M) → L v), ∀ t ∈ S.T,
      {x | x ∈ S.T ∧ S.pi x = S.pi t} = {x | ∃ d ∈ HT, x = S.translate t d} := by sorry

end UniformSubpower.Supplied
