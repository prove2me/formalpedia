-- Prove2me | Theorems.Thm_RobersonCx_corollary_7
-- name    : RobersonCx.corollary_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:13:36.59817+00:00
-- url     : https://prove2.me/theorems/574a1f5c-b390-4502-9862-4541679653a6
-- title:
--   Corollary 7 — prime-order automorphisms with quotient $H$ give $H\in\mathrm{Cl}(\mathcal F)$
-- statement:
--   Let $H$ be a graph, $\mathcal F$ a graph class and $P$ an infinite set of primes. Suppose that for every $p\in P$ there is a graph $F_p\in\mathcal F$ with an automorphism $\sigma_p$ of order $p$ such that $F_p/\langle\sigma_p\rangle\cong H$. Then
--   $$H\in\mathrm{Cl}(\mathcal F).$$
--
--   This is the modular criterion applied to $\mathcal F=\mathrm{Forb}_{\mathrm m}(H)$ and $\mathrm{Forb}_{\mathrm{imm}}(H)$ in Theorem 11.
--
--   Differences from the source:
--   - generalization: a graph class (closed under isomorphism) → any predicate $\mathcal F$ on simple graphs on finite types; reason: an isomorphism-closed class is such a predicate, so the statement specializes to the paper's
--   - encoding: $F_p/\langle\sigma_p\rangle\cong H$ → `QuotIsoTo`: a bijection from the orbits onto $V(H)$ matching quotient adjacency (with loops) to adjacency in $H$; reason: isomorphism of the loop-allowing quotient with a simple graph; same instances
-- source:
--   Kristjánsson, Counterexamples to the Strong Roberson Conjecture, arXiv:2610.03550 (version of 2 November 2026, sha256 1b70a7c6…), Corollary 7, p.8 (PDF p.10)

import Mathlib
import Definitions.Def_RobersonCx_InCl
import Definitions.Def_RobersonCx_QuotIsoTo

set_option autoImplicit false

namespace RobersonCx

/-- Corollary 7 (Kristjánsson, *Counterexamples to the Strong Roberson Conjecture*, arXiv:2610.03550 (version of 2 November 2026, sha256 1b70a7c6…), §3, p.8 (PDF p.10)). Let `H` be a graph, `𝓕` a graph class, and `P` an infinite set of
primes. Suppose that for every `p ∈ P` there is a graph `F_p ∈ 𝓕` with an automorphism `σ_p` of order `p` such
that `F_p/⟨σ_p⟩ ≅ H`. Then `H ∈ Cl(𝓕)`.

**Formalization Note** `F_p/⟨σ_p⟩ ≅ H` is `QuotIsoTo`: a bijection from the orbits onto `V(H)` matching the
quotient adjacency (with loops) to the adjacency of `H`. `𝓕` is any predicate on finite graphs. -/
theorem corollary_7 {W : Type} [Finite W] (H : SimpleGraph W) (𝓕 : GraphClass) (P : Set ℕ)
    (hP : P.Infinite) (hprime : ∀ p ∈ P, p.Prime)
    (hF : ∀ p ∈ P, ∃ (V : Type) (_ : Finite V) (F : SimpleGraph V), 𝓕 V F ∧
      ∃ σ : F ≃g F, orderOf σ = p ∧ QuotIsoTo F σ.toEquiv H) :
    InCl 𝓕 H := by sorry

end RobersonCx
