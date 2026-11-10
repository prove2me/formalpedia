-- Prove2me | Theorems.Thm_UniformSubpower_Supplied_proposition_5_1
-- name    : UniformSubpower.Supplied.proposition_5_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T05:21:21.318521+00:00
-- url     : https://prove2.me/theorems/8180067a-4586-4a87-9a06-af1eb5d4479a
-- title:
--   Proposition 5.1 — the upward-closed structural criterion
-- statement:
--   Let $A_i$ ($i \in \iota$, finitely many) be finite nonempty algebras in one signature with a common Mal'tsev term, let $G \subseteq \prod_i A_i$ be nonempty and $B = \mathrm{Sg}(G)$, with coordinate projections $P_i$, canonical SI variables $W = \{(i, \theta) : \theta \in \mathrm{MI}(P_i)\}$, the all-SI image $\widehat B$ of $B$, and coarse classes $F$ (the $\sim_{gr}$-classes of abelian-monolith variables). For every upward-closed $U \subseteq W$ and every assignment $a_U$ of SI values on $U$,
--   $$a_U \in \widehat B_U \iff \text{all singleton/pair tests of } a_U \text{ pass and } a_{F \cap U} \in \widehat B_{F \cap U} \text{ for every coarse class } F \text{ with } |F \cap U| \ge 3 .$$
--
--   This reduces membership in the projection of the generated relation to its small projections and to the coarse classes, which the rest of the algorithm prepares one at a time. It rests on the structural theorem of Bulatov, Mayr and Szendrei for cube-term (here Mal'tsev) algebras, which is part of what a proof must supply.
--
--   **Formalization Note.** SI values are represented by elements of the coordinate carriers, read modulo $\theta$ (`InHatB`); congruences of $P_i$ are relations on $A_i$ supported on $P_i$; $|F \cap U|$ is `Set.encard`.
--
--   Differences from the source:
--   - encoding: values $a_w \in S_w = P_i/\theta$, congruences of $P_i$ → representatives in $A_i$ read modulo $\theta$, relations on $A_i$ supported on $P_i$; reason: every class has a representative and every notion is invariant under the choice.
--   - encoding: coordinates $1, \dots, n$ and a generator list → a finite index type ι and a nonempty set G; reason: relabelling; a subset of a finite product is finite.
--   - encoding: original nullary symbols replaced by unary constants for nonempty G (§4.1) → nullary symbols kept; reason: the source notes the replacement preserves every generated relation and all congruences.
--   - reading: $\rho_w = (0 : \mu_w)$, formula (6), the join of the principal α with C(µ_w, α; 0) → the join of all congruences α ⊇ θ of $P_i$ with C(µ_w, α; θ); reason: every such α is the join of the principal congruences below it, each of which still satisfies the term condition (it is monotone in α), so the two joins coincide; the term condition is taken in the order C(µ_w, α; ·) printed in (6), which with a Mal'tsev term is symmetric.
-- source:
--   Gkantzounis, Uniform Subpower Membership for Finite Mal'tsev Algebras, STOC 2027 submission (manuscript sha256 149e66b1…), p. 17, Proposition 5.1

import Mathlib
import Definitions.Def_UniformSubpower_Supplied_Algebra
import Definitions.Def_UniformSubpower_Supplied_Congruence

namespace UniformSubpower.Supplied

/-- Proposition 5.1 (Gkantzounis, p. 17): the upward-closed structural criterion. `B = Sg(G)`
in a product of finite nonempty algebras with a common Mal'tsev term, `G` nonempty; an
assignment on an upward-closed `U ⊆ W` lies in `B̂_U` iff it passes the singleton/pair tests and
its restriction to `F ∩ U` lies in `B̂_{F ∩ U}` for every coarse class `F` with `|F ∩ U| ≥ 3`. -/
theorem proposition_5_1 {σ : Signature} {ι : Type} [Fintype ι] {A : ι → Type}
    [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)] (alg : ∀ i, Alg σ (A i))
    (hm : HasCommonMaltsevTerm alg) (G : Set (∀ i, A i)) (hG : G.Nonempty)
    (U : Set (SIVar A)) (hU : UpwardClosed alg G U) (a : ∀ w : SIVar A, A w.1) :
    InHatB alg G U a ↔
      (PairTests alg G U a ∧
        ∀ F : Set (SIVar A), IsCoarseClass alg G F → 3 ≤ (F ∩ U).encard →
          InHatB alg G (F ∩ U) a) := by sorry

end UniformSubpower.Supplied
