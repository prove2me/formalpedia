-- Prove2me | Theorems.Thm_SocialEquilibrium_Existence_exists_equilibrium_point
-- name    : SocialEquilibrium.Existence.exists_equilibrium_point
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T20:44:45.519378+00:00
-- url     : https://prove2.me/theorems/8a4ee18f-4584-4467-9f7b-88fb242f6a2d
-- title:
--   THEOREM (Debreu 1952) — existence of an equilibrium point of a social system
-- statement:
--   Consider finitely many agents $\iota=1,\dots,\nu$. Agent $\iota$ chooses an action $a_\iota$ in a set $\mathfrak A_\iota$ lying in a finite-dimensional real normed space; $\bar a_\iota$ denotes the actions of the others, ranging over $\bar{\mathfrak A}_\iota=\prod_{j\ne\iota}\mathfrak A_j$. Given $\bar a_\iota$, agent $\iota$ is restricted to a non-void set $A_\iota(\bar a_\iota)\subseteq\mathfrak A_\iota$, and receives the payoff $f_\iota(\bar a_\iota,a_\iota)$ in the completed real line $\overline{\mathbb R}$. Write
--   $$\varphi_\iota(\bar a_\iota)=\max_{a_\iota\in A_\iota(\bar a_\iota)}f_\iota(\bar a_\iota,a_\iota),\qquad M_{\bar a_\iota}=\{a_\iota\in A_\iota(\bar a_\iota)\mid f_\iota(\bar a_\iota,a_\iota)=\varphi_\iota(\bar a_\iota)\}.$$
--   Assume that for every $\iota$:
--
--   1. $\mathfrak A_\iota$ is a contractible polyhedron;
--   2. the graph $G_\iota=\{(\bar a_\iota,a_\iota)\mid a_\iota\in A_\iota(\bar a_\iota)\}$ is closed in $\bar{\mathfrak A}_\iota\times\mathfrak A_\iota$;
--   3. $f_\iota$ is continuous on $G_\iota$;
--   4. $\varphi_\iota$ is continuous on $\bar{\mathfrak A}_\iota$;
--   5. $M_{\bar a_\iota}$ is contractible for every $\bar a_\iota$.
--
--   Then there exists an **equilibrium point**: a profile $a^*$ such that for all $\iota$
--   $$a^*_\iota\in A_\iota(\bar a^*_\iota)\quad\text{and}\quad f_\iota(a^*)=\max_{a_\iota\in A_\iota(\bar a^*_\iota)}f_\iota(\bar a^*_\iota,a_\iota).$$
--
--   This is the main theorem of Debreu (1952). It contains Nash's existence theorem for $N$-person games, and Arrow and Debreu (1954) used it to prove the existence of a competitive equilibrium.
--
--   **Formalization Note** The non-void values of $A_\iota$ are Debreu's standing assumption ("For any $\bar a_\iota$, $A_\iota(\bar a_\iota)$ is always understood to be non-void", p. 888) and appear as an explicit hypothesis. $\varphi_\iota$ is written as a supremum in `EReal`, which is Debreu's Max whenever the maximum is attained. The compactness of $A_\iota(\bar a_\iota)$ and the continuity of $f_\iota$ in $a_\iota$, which the paper's informal background mentions, follow from hypotheses 1–3 and are not added. The others' actions form a product over the agents $j\ne\iota$, so $A_\iota$ cannot depend on agent $\iota$'s own action.
-- source:
--   Debreu, A Social Equilibrium Existence Theorem, Proc. Natl. Acad. Sci. USA 38(10), 1952, p. 888, THEOREM (§2 Equilibrium Points)

import Mathlib
import Definitions.Def_SocialEquilibrium_Existence_IsPolyhedron
import Definitions.Def_SocialEquilibrium_Existence_IsContractible
import Definitions.Def_SocialEquilibrium_Existence_graph
import Definitions.Def_SocialEquilibrium_Existence_Game

namespace SocialEquilibrium.Existence

/-- Debreu (1952), §2, p. 888, THEOREM (social equilibrium existence). For every agent `ι`, let
`𝔄_ι` be a contractible polyhedron, `A_ι` a multi-valued function from `𝔄̄_ι` to `𝔄_ι` with
non-void values whose graph `G_ι` is closed, `f_ι` a function continuous on `G_ι` with values in
the completed real line such that `φ_ι(ā_ι) = Max_{a_ι ∈ A_ι(ā_ι)} f_ι(ā_ι, a_ι)` is continuous.
If every `M_{ā_ι}` is contractible, then there exists an equilibrium point. -/
theorem exists_equilibrium_point {ι : Type*} [Fintype ι] [DecidableEq ι]
    {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    [∀ i, FiniteDimensional ℝ (E i)]
    (X : ∀ i, Set (E i)) (hX : ∀ i, IsPolyhedron (X i) ∧ IsContractible (X i))
    (A : ∀ i : ι, Others X i → Set (X i))
    (hA : ∀ i (ā : Others X i), (A i ā).Nonempty)
    (hG : ∀ i, IsClosed (graph (A i)))
    (f : ι → (∀ j, X j) → EReal)
    (hf : ∀ i, ContinuousOn (fun p : Others X i × X i => f i (join X i p.1 p.2)) (graph (A i)))
    (hφ : ∀ i, Continuous (bestValue X A f i))
    (hM : ∀ i (ā : Others X i), IsContractible (bestSet X A f i ā)) :
    ∃ a : ∀ j, X j, IsEquilibrium X A f a := by sorry

end SocialEquilibrium.Existence
