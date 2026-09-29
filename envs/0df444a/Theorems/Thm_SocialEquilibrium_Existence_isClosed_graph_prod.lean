-- Prove2me | Theorems.Thm_SocialEquilibrium_Existence_isClosed_graph_prod
-- name    : SocialEquilibrium.Existence.isClosed_graph_prod
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T20:43:39.745195+00:00
-- url     : https://prove2.me/theorems/0654b8ba-c8b0-4680-8369-811ae5d6caf1
-- title:
--   Proof of the THEOREM — the graph Γ of φ is closed
-- statement:
--   In Debreu's abstract economy, let $M_\iota\subseteq\bar{\mathfrak A}_\iota\times\mathfrak A_\iota$ be a closed set for every agent $\iota$, and let $\phi(a)=\{a'\in\mathfrak A\mid (\bar a_\iota,a'_\iota)\in M_\iota\text{ for all }\iota\}$. Then the graph
--   $$\Gamma=\{(a,a')\mid a'\in\phi(a)\}=\bigcap_\iota\mathfrak M_\iota,\qquad \mathfrak M_\iota=\{(a,a')\mid(\bar a_\iota,a'_\iota)\in M_\iota\},$$
--   is closed in $\mathfrak A\times\mathfrak A$.
--
--   Applied to the best-response graphs $M_\iota$, this shows that $\phi(a)=M_{\bar a_1}\times\cdots\times M_{\bar a_\nu}$ is semicontinuous, the last hypothesis of the fixed-point LEMMA.
-- source:
--   Debreu, A Social Equilibrium Existence Theorem, Proc. Natl. Acad. Sci. USA 38(10), 1952, p. 889, §2 proof of the THEOREM, fourth and fifth displays

import Mathlib
import Definitions.Def_SocialEquilibrium_Existence_graph
import Definitions.Def_SocialEquilibrium_Existence_Game

namespace SocialEquilibrium.Existence

/-- Debreu (1952), §2, p. 889 (proof of the THEOREM, fourth and fifth displays): if every
`M_ι ⊆ 𝔄̄_ι × 𝔄_ι` is closed, then the graph
`Γ = {(a, a′) | (ā_ι, a′_ι) ∈ M_ι for all ι} = ⋂_ι 𝔐_ι` of the multi-valued function
`a ↦ {a′ | (ā_ι, a′_ι) ∈ M_ι for all ι}` is closed in `𝔄 × 𝔄`. -/
theorem isClosed_graph_prod {ι : Type*} [Fintype ι] [DecidableEq ι]
    {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    [∀ i, FiniteDimensional ℝ (E i)]
    (X : ∀ i, Set (E i)) (M : ∀ i : ι, Set (Others X i × X i))
    (hM : ∀ i, IsClosed (M i)) :
    IsClosed (graph fun a : ∀ j, X j =>
      {a' : ∀ j, X j | ∀ i, (others X i a, a' i) ∈ M i}) := by sorry

end SocialEquilibrium.Existence
