-- Prove2me | Theorems.Thm_SKAlgorithm_Qudit_base_case
-- name    : SKAlgorithm.Qudit.base_case
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T02:26:54.818555+00:00
-- url     : https://prove2.me/theorems/1e439eae-2f2a-44fe-8b2f-340a301cacdb
-- title:
--   p. 5 (and p. 11) — basic ε₀-approximations of bounded length l₀
-- statement:
--   Let $\mathcal G$ be an instruction set for $SU(d)$ and let $\epsilon_0 > 0$. Then there is a length $l_0 \in \mathbb N$ such that every gate $U \in SU(d)$ has an $\epsilon_0$-approximation by a sequence of gates from $\mathcal G$ of length at most $l_0$:
--   $$\forall U \in SU(d)\ \exists S \subseteq \mathcal G^{*},\quad |S| \le l_0 \ \text{ and } \ d(U, S) < \epsilon_0 .$$
--
--   This is the preprocessing stage of the Solovay-Kitaev algorithm ("Return Basic Approximation to $U$"): the paper obtains it by enumerating all instruction sequences up to a sufficiently large but fixed length $l_0$. It supplies the depth-zero case of the recursion with a length independent of $U$.
--
--   **Formalization Note.** The bound $l_0$ is chosen before $U$; it depends only on $\mathcal G$ and $\epsilon_0$. No compactness hypothesis is added; compactness of $SU(d)$ is a fact to be proved, not assumed.
-- source:
--   Dawson and Nielsen, The Solovay-Kitaev algorithm, arXiv:quant-ph/0505030v2, p. 5, §3, base case 'In order to implement this step …'; p. 11, §5.1, 'This is done by enumerating all possible gate sequences up to some sufficient length'

import Mathlib
import Definitions.Def_SKAlgorithm_Qudit_Model

open scoped Matrix
open QAlgorithms

namespace SKAlgorithm.Qudit

theorem base_case {d : ℕ} (G : Finset (SU d)) (hG : IsInstructionSet G)
    (ε₀ : ℝ) (hε₀ : 0 < ε₀) :
    ∃ l₀ : ℕ, ∀ U : SU d, ∃ S : List (SU d), (∀ g ∈ S, g ∈ G) ∧ S.length ≤ l₀ ∧
      opDist U (seqUnitary S) < ε₀ := by sorry

end SKAlgorithm.Qudit
