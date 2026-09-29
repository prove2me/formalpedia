-- Prove2me | Theorems.Thm_SocialEquilibrium_Existence_bestValue_continuousAt
-- name    : SocialEquilibrium.Existence.bestValue_continuousAt
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T20:46:26.725129+00:00
-- url     : https://prove2.me/theorems/d3b902ac-da8b-42f1-b585-b45869acf3af
-- title:
--   Remark — continuity of the best value φ_ι
-- statement:
--   In Debreu's abstract economy, fix an agent $\iota$ and a point $\bar a^0_\iota$. If $A_\iota$ (with non-void values) has a compact graph $G_\iota$ and is continuous at $\bar a^0_\iota$, and $f_\iota$ is a continuous function from $G_\iota$ to the completed real line, then
--   $$\varphi_\iota(\bar a_\iota)=\max_{a_\iota\in A_\iota(\bar a_\iota)}f_\iota(\bar a_\iota,a_\iota)$$
--   is continuous at $\bar a^0_\iota$.
--
--   The continuity of $\varphi_\iota$ is a joint hypothesis on $f_\iota$ and $A_\iota$ in the THEOREM; the Remark replaces it by conditions on each of them separately, and is what the COROLLARY on saddle points uses.
-- source:
--   Debreu, A Social Equilibrium Existence Theorem, Proc. Natl. Acad. Sci. USA 38(10), 1952, p. 889, Remark

import Mathlib
import Definitions.Def_SocialEquilibrium_Existence_graph
import Definitions.Def_SocialEquilibrium_Existence_Game

namespace SocialEquilibrium.Existence

/-- Debreu (1952), §2, p. 889, Remark: if `A_ι` (with non-void values) has a compact graph `G_ι`
and is continuous at `ā⁰_ι`, and `f_ι` is a continuous function from `G_ι` to the completed real
line, then `φ_ι` is continuous at `ā⁰_ι`. -/
theorem bestValue_continuousAt {ι : Type*} [Fintype ι] [DecidableEq ι]
    {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    [∀ i, FiniteDimensional ℝ (E i)]
    (X : ∀ i, Set (E i)) (A : ∀ i : ι, Others X i → Set (X i))
    (f : ι → (∀ j, X j) → EReal) (i : ι) (ā₀ : Others X i)
    (hA : ∀ ā : Others X i, (A i ā).Nonempty)
    (hG : IsCompact (graph (A i)))
    (hf : ContinuousOn (fun p : Others X i × X i => f i (join X i p.1 p.2)) (graph (A i)))
    (hAc : ConstraintContinuousAt A i ā₀) :
    ContinuousAt (bestValue X A f i) ā₀ := by sorry

end SocialEquilibrium.Existence
