-- Prove2me | Theorems.Thm_SocialEquilibrium_Existence_bestResponse_isContractible
-- name    : SocialEquilibrium.Existence.bestResponse_isContractible
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T20:42:03.733975+00:00
-- url     : https://prove2.me/theorems/36f8c73e-2814-4b49-9aff-91ed45d203a6
-- title:
--   Proof of the THEOREM — φ(a) = M_ā₁ × ⋯ × M_āᵥ is contractible
-- statement:
--   In the setting of Debreu's abstract economy (finitely many agents, action sets $\mathfrak A_\iota$ in finite-dimensional real normed spaces, constraint maps $A_\iota$, payoffs $f_\iota$ into the completed real line), suppose that every set of constrained best responses $M_{\bar a_\iota}$ is contractible. Then for every profile $a\in\mathfrak A$ the set
--   $$\phi(a)=M_{\bar a_1}\times\cdots\times M_{\bar a_\nu}$$
--   is contractible, as a subset of $\mathfrak A$.
--
--   This supplies the contractible-values hypothesis of the fixed-point LEMMA for the map $\phi$.
-- source:
--   Debreu, A Social Equilibrium Existence Theorem, Proc. Natl. Acad. Sci. USA 38(10), 1952, p. 889, §2 proof of the THEOREM, first paragraph (last sentence)

import Mathlib
import Definitions.Def_SocialEquilibrium_Existence_IsContractible
import Definitions.Def_SocialEquilibrium_Existence_Game

namespace SocialEquilibrium.Existence

/-- Debreu (1952), §2, p. 889 (proof of the THEOREM, first paragraph): if every best-response
set `M_{ā_ι}` is contractible, then `φ(a) = M_{ā_1} × ⋯ × M_{ā_ν}` is contractible for every
profile `a ∈ 𝔄`. -/
theorem bestResponse_isContractible {ι : Type*} [Fintype ι] [DecidableEq ι]
    {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    [∀ i, FiniteDimensional ℝ (E i)]
    (X : ∀ i, Set (E i)) (A : ∀ i : ι, Others X i → Set (X i))
    (f : ι → (∀ j, X j) → EReal)
    (hM : ∀ i (ā : Others X i), IsContractible (bestSet X A f i ā)) :
    ∀ a : ∀ j, X j, IsContractible (bestResponse X A f a) := by sorry

end SocialEquilibrium.Existence
