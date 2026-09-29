-- Prove2me | Theorems.Thm_SocialEquilibrium_Existence_bestValue_upperSemicontinuousAt
-- name    : SocialEquilibrium.Existence.bestValue_upperSemicontinuousAt
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T20:45:34.426556+00:00
-- url     : https://prove2.me/theorems/32f8b426-639b-4282-a9a8-42c3fbd7e6a8
-- title:
--   Remark, step (α) — the best value φ_ι is upper semicontinuous
-- statement:
--   In Debreu's abstract economy, fix an agent $\iota$ and a point $\bar a^0_\iota\in\bar{\mathfrak A}_\iota$. Suppose that $A_\iota$ has non-void values and a compact graph $G_\iota$, and that $f_\iota$ is continuous on $G_\iota$ with values in the completed real line. Then the best value
--   $$\varphi_\iota(\bar a_\iota)=\max_{a_\iota\in A_\iota(\bar a_\iota)}f_\iota(\bar a_\iota,a_\iota)$$
--   is upper semicontinuous at $\bar a^0_\iota$: for every sequence $\bar a^n_\iota\to\bar a^0_\iota$ and every $\varepsilon>0$, eventually $\varphi_\iota(\bar a^n_\iota)<\varphi_\iota(\bar a^0_\iota)+\varepsilon$.
--
--   **Formalization Note** The conclusion is Mathlib's `UpperSemicontinuousAt`, which the paper itself names ("in other words, $\varphi(\bar a)$ is upper semicontinuous at $\bar a^0$"). Mathlib's definition uses strict upper bounds in `EReal` and involves no arithmetic with $\pm\infty$; the paper reaches the same statement by transporting $\overline{\mathbb R}$ to $[-1,1]$.
-- source:
--   Debreu, A Social Equilibrium Existence Theorem, Proc. Natl. Acad. Sci. USA 38(10), 1952, p. 890, proof of the Remark, step (α)

import Mathlib
import Definitions.Def_SocialEquilibrium_Existence_graph
import Definitions.Def_SocialEquilibrium_Existence_Game

namespace SocialEquilibrium.Existence

/-- Debreu (1952), §2, p. 890, step (α) of the proof of the Remark: if `A_ι` has non-void values
and a compact graph `G_ι` and `f_ι` is continuous on `G_ι` (values in the completed real line),
then `φ_ι` is upper semicontinuous at every `ā⁰_ι`. -/
theorem bestValue_upperSemicontinuousAt {ι : Type*} [Fintype ι] [DecidableEq ι]
    {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    [∀ i, FiniteDimensional ℝ (E i)]
    (X : ∀ i, Set (E i)) (A : ∀ i : ι, Others X i → Set (X i))
    (f : ι → (∀ j, X j) → EReal) (i : ι) (ā₀ : Others X i)
    (hA : ∀ ā : Others X i, (A i ā).Nonempty)
    (hG : IsCompact (graph (A i)))
    (hf : ContinuousOn (fun p : Others X i × X i => f i (join X i p.1 p.2)) (graph (A i))) :
    UpperSemicontinuousAt (bestValue X A f i) ā₀ := by sorry

end SocialEquilibrium.Existence
