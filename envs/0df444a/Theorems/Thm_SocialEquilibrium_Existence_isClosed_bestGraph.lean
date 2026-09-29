-- Prove2me | Theorems.Thm_SocialEquilibrium_Existence_isClosed_bestGraph
-- name    : SocialEquilibrium.Existence.isClosed_bestGraph
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T20:43:05.765762+00:00
-- url     : https://prove2.me/theorems/c8efc41e-0525-450d-8fa9-be4d899f761e
-- title:
--   Proof of the THEOREM — the best-response graph M_ι is closed
-- statement:
--   In Debreu's abstract economy, fix an agent $\iota$. Suppose the graph $G_\iota=\{(\bar a_\iota,a_\iota)\mid a_\iota\in A_\iota(\bar a_\iota)\}$ is closed in $\bar{\mathfrak A}_\iota\times\mathfrak A_\iota$, that $(\bar a_\iota,a_\iota)\mapsto f_\iota(\bar a_\iota,a_\iota)$ is continuous on $G_\iota$, and that the best value $\varphi_\iota$ is continuous on $\bar{\mathfrak A}_\iota$. Then the set
--   $$M_\iota=\{(\bar a_\iota,a_\iota)\mid a_\iota\in M_{\bar a_\iota}\}=\{(\bar a_\iota,a_\iota)\in G_\iota\mid f_\iota(\bar a_\iota,a_\iota)=\varphi_\iota(\bar a_\iota)\}$$
--   is closed in $\bar{\mathfrak A}_\iota\times\mathfrak A_\iota$.
--
--   This is the per-agent step towards the closed graph of the best-response map $\phi$.
-- source:
--   Debreu, A Social Equilibrium Existence Theorem, Proc. Natl. Acad. Sci. USA 38(10), 1952, p. 889, §2 proof of the THEOREM, second and third displays

import Mathlib
import Definitions.Def_SocialEquilibrium_Existence_graph
import Definitions.Def_SocialEquilibrium_Existence_Game

namespace SocialEquilibrium.Existence

/-- Debreu (1952), §2, p. 889 (proof of the THEOREM, second and third displays): if the graph
`G_ι` of `A_ι` is closed, `f_ι` is continuous on `G_ι` and `φ_ι` is continuous, then
`M_ι = {(ā_ι, a_ι) | a_ι ∈ M_{ā_ι}} = {(ā_ι, a_ι) ∈ G_ι | f_ι(ā_ι, a_ι) = φ_ι(ā_ι)}` is closed in
`𝔄̄_ι × 𝔄_ι`. -/
theorem isClosed_bestGraph {ι : Type*} [Fintype ι] [DecidableEq ι]
    {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    [∀ i, FiniteDimensional ℝ (E i)]
    (X : ∀ i, Set (E i)) (A : ∀ i : ι, Others X i → Set (X i))
    (f : ι → (∀ j, X j) → EReal) (i : ι)
    (hG : IsClosed (graph (A i)))
    (hf : ContinuousOn (fun p : Others X i × X i => f i (join X i p.1 p.2)) (graph (A i)))
    (hφ : Continuous (bestValue X A f i)) :
    IsClosed (graph (bestSet X A f i)) := by sorry

end SocialEquilibrium.Existence
