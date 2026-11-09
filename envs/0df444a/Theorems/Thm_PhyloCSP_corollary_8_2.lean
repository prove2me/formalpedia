-- Prove2me | Theorems.Thm_PhyloCSP_corollary_8_2
-- name    : PhyloCSP.corollary_8_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:24:17.904184+00:00
-- url     : https://prove2.me/theorems/92efd2e2-3fb5-4c53-ac82-448f197970c1
-- title:
--   Corollary 8.2 — $\mathrm{Aut}(\mathcal F)$-invariant families are exchangeable
-- statement:
--   Let $(X_x)_{x\in Z}$ be random variables indexed by the leaves of the Fraïssé limit, taking values in a standard Borel space $\beta$, and invariant under $\mathrm{Aut}(\mathcal F)$: for every automorphism $g$, the families $(X_{g(x)})_{x\in Z}$ and $(X_x)_{x\in Z}$ have the same joint distribution. Then the family is exchangeable: for every permutation $\sigma$ of $Z$ moving only finitely many leaves (not necessarily an automorphism), $(X_{\sigma(x)})_{x}$ has the same joint distribution as $(X_x)_x$.
--
--   The paper states this for real-valued variables and for variables whose values are finite or countable sequences of real numbers; all of these are standard Borel. It allows de Finetti's theorem to be applied to invariant random variables on $\mathcal F$.
--
--   Differences from the source:
--   - generalization: real-valued variables, and variables whose values are finite or countable sequences of reals → variables with values in an arbitrary standard Borel space β; reason: ℝ, ℝⁿ, the finite sequences and ℝ^ℕ are standard Borel, so both sentences are special cases
--   - encoding: Aut(F)-invariant family; exchangeable → equality of the push-forward laws on Z → β for g ∈ AutF and for finitely supported permutations of Z; reason: standard measure-theoretic reading
--   - encoding: the Fraïssé limit F = (Z, C) and its automorphism group Aut(F) → the concrete structure (Z, fraisseRel) of Definition 7.5, Z = Finset ℚ, and AutF its automorphism group; reason: Theorem 7.4 and Appendix B.1 identify the concrete structure with F, which is unique up to isomorphism; the statement is invariant under isomorphism
-- source:
--   Makarychev, Approximation Algorithms for Satisfiable Phylogenetic CSPs, STOC 2027 submission (manuscript sha256 3444b6c029bce73ce9a6ad0ae6bc8386c291dcb0b1e504e8216c60cd4d682dac), Corollary 8.2, p.25 (PDF p.27)

import Mathlib
import Definitions.Def_PhyloCSP_AutF

set_option autoImplicit false

open MeasureTheory

namespace PhyloCSP

/-- Makarychev, *Approximation Algorithms for Satisfiable Phylogenetic CSPs*, STOC 2027
submission (manuscript sha256 3444b6c0…682dac), Corollary 8.2, p.25 (PDF p.27): "Every
Aut(F)-invariant family (Xx)x∈Z of real-valued random variables is exchangeable. The same holds for
random variables whose values are finite or countable sequences of real numbers." Invariance
(p.24): "for every g ∈ Aut(F), the families (Xx)x∈Z and (Xg(x))x∈Z have the same joint
distribution"; exchangeable: the joint law is unchanged by every permutation of finitely many
indices.

**Formalization Note.** The values lie in an arbitrary standard Borel space `β`; this covers `ℝ`,
`ℝⁿ`, finite sequences and `ℝ^ℕ`, hence both sentences. Joint laws are push-forwards to `Z → β`
with the product σ-algebra; permutations of `Z` moving finitely many leaves need not preserve the
tree structure. -/
theorem corollary_8_2 {Ω β : Type} [MeasurableSpace Ω] [MeasurableSpace β] [StandardBorelSpace β]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Z → Ω → β) (hX : ∀ x, Measurable (X x))
    (hinv : ∀ g ∈ AutF, P.map (fun ω x => X (g x) ω) = P.map (fun ω x => X x ω)) :
    ∀ σ : Equiv.Perm Z, {x | σ x ≠ x}.Finite →
      P.map (fun ω x => X (σ x) ω) = P.map (fun ω x => X x ω) := by sorry

end PhyloCSP
