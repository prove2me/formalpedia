-- Prove2me | Theorems.Thm_ShapleyScarf_CoreExistence_balanced_game_core_nonempty
-- name    : ShapleyScarf.CoreExistence.balanced_game_core_nonempty
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T14:38:31.124375+00:00
-- url     : https://prove2.me/theorems/2896470f-7099-4635-8135-836f85469761
-- title:
--   Section 3 — a balanced NTU game has a nonempty core
-- statement:
--   Let $N$ be any finite nonempty player set and let $V(S)\subseteq\mathbb R^N$ be the payoff set of coalition $S$. For every nonempty $S$, assume: (a) $V(S)$ is closed; (b) membership is preserved by decreasing the coordinates in $S$, with all other coordinates arbitrary; and (c)
--
--   $$\left[V(S)\setminus\bigcup_{i\in S}\operatorname{int}V(\{i\})\right]\cap E^S$$
--
--   is bounded and nonempty, where $E^S$ is the subspace of vectors zero outside $S$. Assume also (e): every balanced family $T$ satisfies $\bigcap_{S\in T}V(S)\subseteq V(N)$. Here balance means nonnegative weights $\delta_S$, zero off $T$, with $\sum_{S\ni j}\delta_S=1$ for every player $j$; zero weights within $T$ are permitted.
--
--   Then the payoff core is nonempty:
--
--   $$C(V)=V(N)\setminus\bigcup_{\varnothing\ne S\subseteq N}\operatorname{int}_{\mathbb R^N}V(S)\ne\varnothing.$$
--
--   This is the general theorem invoked for the paper's core-existence consequence. It applies to nonconvex NTU games and requires neither superadditivity nor finite generation. The characteristic function is arbitrary subject to exactly (a)–(c) and (e).
--
--   **Formalization Note.** The published predicate `IsBalancedGame` contains all four conditions; core nonemptiness is a conclusion, with no market or TTC assumption.
--
--   Differences from the source:
--   - reading: the core display starts with the free expression V(S) → the feasible term is V(N); reason: the immediately following sentence explicitly defines the core using V(N), including N among blocking coalitions
--   - encoding: a finite nonempty player set and its Euclidean payoff space → a type N with Fintype, DecidableEq and Nonempty, and the finite product N → ℝ; reason: finite indexing and decidable membership change no market or game instance; the product topology is the Euclidean topology
-- source:
--   Shapley and Scarf, On cores and indivisibility, Journal of Mathematical Economics 1 (1974), published, DOI 10.1016/0304-4068(74)90033-0, https://doi.org/10.1016/0304-4068(74)90033-0; Section 3, fundamental theorem after condition (e), printed p. 109 / PDF p. 6; standing conditions (a)–(c), printed p. 107 / PDF p. 4; core definition, printed p. 108 / PDF p. 5.

import Mathlib
import Definitions.Def_ShapleyScarf_Balanced_BalancedGame
import Definitions.Def_ShapleyScarf_CoreExistence_payoffCore

namespace ShapleyScarf.CoreExistence

/-- Section 3, fundamental theorem after (e), printed p. 109 / PDF p. 6.
The game predicate includes exactly (a)–(c) and (e), with no convexity,
superadditivity, finite-generation or market assumption. The core follows the explicit
grand-coalition reading of the prose at printed p. 108 / PDF p. 5. -/
theorem balanced_game_core_nonempty
    {N : Type*} [Fintype N] [DecidableEq N] [Nonempty N]
    (V : Finset N → Set (N → ℝ))
    (hV : ShapleyScarf.Balanced.IsBalancedGame V) :
    (payoffCore V).Nonempty := by sorry

end ShapleyScarf.CoreExistence
