-- Prove2me | Theorems.Thm_PacingComplexity_approx_pacing_ppad_hard
-- name    : PacingComplexity.approx_pacing_ppad_hard
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:29:03.594985+00:00
-- url     : https://prove2.me/theorems/33c989bb-2ecc-443e-9e14-63e758722818
-- title:
--   Theorem 2: approximate pacing equilibria are PPAD-hard to find for $\delta=\gamma=1/n^c$
-- statement:
--   For a real $c>0$, let APPROX-PACING$_c$ be the search problem whose instances are rational second-price pacing games with $n\ge2$ buyers and whose answers are rational $(\delta,\gamma)$-approximate pacing equilibria with
--   $$
--   \delta=\gamma=\frac1{n^c},
--   $$
--   $n$ being the number of buyers. Let WIN-LOSE-WSNE be the problem of finding a $\tfrac1n$-well-supported Nash equilibrium of an $n\times n$ bimatrix game with costs in $\{0,1\}$.
--
--   **Theorem.** For every real $c>0$ and every search problem $Q$: if $Q$ reduces in polynomial time to WIN-LOSE-WSNE, then $Q$ reduces in polynomial time to APPROX-PACING$_c$.
--
--   Since WIN-LOSE-WSNE is PPAD-hard (Chen et al. 2007), finding a $(1/n^c,1/n^c)$-approximate pacing equilibrium in a second-price pacing game is PPAD-hard for every constant $c>0$. Together with the paper's Theorem 1 (membership in PPAD) this makes the problem PPAD-complete, and it answers the open question of Conitzer et al. on the complexity of pacing equilibria in second-price auctions.
--
--   **Formalization Note** A polynomial-time reduction is a pair of polynomial-time maps on Cook Turing machines: an instance map and an answer map that is correct for every answer of the target problem. The reduction may depend on $c$.
--
--   Differences from the source:
--   - generalization: "PPAD-hard" (no definition of PPAD or of its reductions in the paper) → every search problem that reduces in polynomial time to WIN-LOSE-WSNE also reduces to APPROX-PACING; reason: by Chen et al. 2007 every PPAD problem reduces to WIN-LOSE-WSNE, so this yields the theorem for any reduction-based definition of PPAD-hardness, with no formal PPAD class
--   - reading: the PPAD-hardness of WIN-LOSE-WSNE (Chen et al. 2007), cited and not proved → it enters only through the hypothesis on Q; reason: the paper's conclusion rests on that citation and Lean has no proof of it
--   - encoding: rational games (p.3), computation unspecified → binary-encoded strings, Cook Turing machines, reductions correct for every answer, target instances with n ≥ 2 buyers; reason: the standard meaning of PPAD reductions; Definition 2 needs δ < 1 and the second bid needs two buyers, so n ≥ 2 only excludes undefined instances
--   - encoding: (α, x) real in Definition 2 (p.7), (x, y) real in Δn (p.30) → answers are binary codes of rational vectors satisfying the same real predicates; reason: answers are finite strings; this loses nothing: p.3 gives a rational exact pacing equilibrium of every rational game, and every rational bimatrix game has a rational Nash equilibrium
-- source:
--   Chen, Kroer, Kumar, The Complexity of Pacing for Second-Price Auctions, arXiv:2103.13969v2, Theorem 2, p.3 (proof: p.16, 'Theorem 2 follows from Theorem 3 by standard padding arguments', and Appendix A)

import Mathlib
import Definitions.Def_TetrisHard_Rows_Search
import Definitions.Def_CardinalMatching_SearchReduces
import Definitions.Def_PacingComplexity_WinLoseWSNE
import Definitions.Def_PacingComplexity_ApproxPacing

namespace PacingComplexity

open CardinalMatching

/-- **Theorem 2** (Chen, Kroer, Kumar, *The Complexity of Pacing for Second-Price Auctions*,
arXiv:2103.13969v2, p.3; proof p.16 and Appendix A): "For any constant c > 0, finding a
(δ, γ)-approximate pacing equilibrium in a second-price pacing game with n players is PPAD-hard
when δ = γ = 1/n^c."

Stated as a reduction closure: for every real `c > 0`, every search problem `Q` that reduces in
polynomial time to WIN-LOSE-WSNE (a `1/n`-well-supported Nash equilibrium of an `n × n` bimatrix
game with costs in `{0, 1}`) also reduces in polynomial time to APPROX-PACING_c (a
`(δ, γ)`-approximate pacing equilibrium, `δ = γ = n^(−c)` with `n` the number of buyers, of a
rational SPP game with `n ≥ 2` buyers).

**Formalization Note** The paper's proof rests on the PPAD-hardness of WIN-LOSE-WSNE (Chen et al.
2007, cited on pp.30 and 34), which says that every PPAD problem satisfies the hypothesis; so this
statement gives Theorem 2 for any definition of PPAD-hardness by polynomial-time search reductions
from PPAD, without a formal PPAD class. Reductions are `SearchReduces` (Cook's Turing machines,
correct for every answer); encodings are binary. -/
theorem approx_pacing_ppad_hard (c : ℝ) (hc : 0 < c) (Q : TetrisHard.Rows.SearchProblem)
    (hQ : SearchReduces Q WinLoseWSNE) :
    SearchReduces Q (ApproxPacing c) := by sorry

end PacingComplexity
