-- Prove2me | Theorems.Thm_SocialEquilibrium_Existence_bestValue_lowerSemicontinuousAt
-- name    : SocialEquilibrium.Existence.bestValue_lowerSemicontinuousAt
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T20:46:02.620753+00:00
-- url     : https://prove2.me/theorems/d5cba6d4-c525-4636-b98c-fdd9731cc261
-- title:
--   Remark, step (β) — the best value φ_ι is lower semicontinuous where A_ι is continuous
-- statement:
--   In Debreu's abstract economy, fix an agent $\iota$ and a point $\bar a^0_\iota$. Suppose that $A_\iota$ has non-void values and a compact graph $G_\iota$, that $f_\iota$ is continuous on $G_\iota$ with values in the completed real line, and in addition that $A_\iota$ is continuous at $\bar a^0_\iota$: for every $a^0_\iota\in A_\iota(\bar a^0_\iota)$ and every sequence $\bar a^n_\iota\to\bar a^0_\iota$ there is a sequence $a^n_\iota\to a^0_\iota$ with $a^n_\iota\in A_\iota(\bar a^n_\iota)$. Then the best value $\varphi_\iota$ is lower semicontinuous at $\bar a^0_\iota$: for every sequence $\bar a^n_\iota\to\bar a^0_\iota$ and every $\varepsilon>0$, eventually
--   $$\varphi_\iota(\bar a^n_\iota)>\varphi_\iota(\bar a^0_\iota)-\varepsilon.$$
--
--   **Formalization Note** The conclusion is Mathlib's `LowerSemicontinuousAt`, which the paper itself names. No subtraction in `EReal` is used.
-- source:
--   Debreu, A Social Equilibrium Existence Theorem, Proc. Natl. Acad. Sci. USA 38(10), 1952, p. 890, proof of the Remark, step (β)

import Mathlib
import Definitions.Def_SocialEquilibrium_Existence_graph
import Definitions.Def_SocialEquilibrium_Existence_Game

namespace SocialEquilibrium.Existence

/-- Debreu (1952), §2, p. 890, step (β) of the proof of the Remark: if in addition to the
hypotheses of (α) the multi-valued function `A_ι` is continuous at `ā⁰_ι`, then `φ_ι` is lower
semicontinuous at `ā⁰_ι`. -/
theorem bestValue_lowerSemicontinuousAt {ι : Type*} [Fintype ι] [DecidableEq ι]
    {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    [∀ i, FiniteDimensional ℝ (E i)]
    (X : ∀ i, Set (E i)) (A : ∀ i : ι, Others X i → Set (X i))
    (f : ι → (∀ j, X j) → EReal) (i : ι) (ā₀ : Others X i)
    (hA : ∀ ā : Others X i, (A i ā).Nonempty)
    (hG : IsCompact (graph (A i)))
    (hf : ContinuousOn (fun p : Others X i × X i => f i (join X i p.1 p.2)) (graph (A i)))
    (hAc : ConstraintContinuousAt A i ā₀) :
    LowerSemicontinuousAt (bestValue X A f i) ā₀ := by sorry

end SocialEquilibrium.Existence
