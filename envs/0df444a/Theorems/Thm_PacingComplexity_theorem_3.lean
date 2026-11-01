-- Prove2me | Theorems.Thm_PacingComplexity_theorem_3
-- name    : PacingComplexity.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:28:59.664161+00:00
-- url     : https://prove2.me/theorems/8b93bcdf-1b2a-4b06-a7b8-e3a2ad36ab4a
-- title:
--   Theorem 3: computing a $(1/n^7,1/n^7)$-approximate pacing equilibrium is PPAD-hard
-- statement:
--   Let APPROX-PACING$_7$ be the search problem whose instances are rational SPP games with $n\ge2$ buyers and whose answers are rational $(\delta,\gamma)$-approximate pacing equilibria with
--   $$
--   \delta=\gamma=\frac1{n^7},
--   $$
--   $n$ being the number of buyers. Let WIN-LOSE-WSNE be the problem of finding a $\tfrac1n$-well-supported Nash equilibrium of an $n\times n$ bimatrix game with costs in $\{0,1\}$.
--
--   **Theorem.** Every search problem $Q$ that reduces in polynomial time to WIN-LOSE-WSNE also reduces in polynomial time to APPROX-PACING$_7$.
--
--   Since WIN-LOSE-WSNE is PPAD-hard (Chen et al. 2007), this says that computing a $(1/n^7,1/n^7)$-approximate pacing equilibrium is PPAD-hard. Theorem 2 follows from it by padding with dummy buyers.
--
--   **Formalization Note** A polynomial-time reduction is a pair of polynomial-time maps on Cook Turing machines: an instance map and an answer map that is correct for every answer of the target problem.
--
--   Differences from the source:
--   - generalization: "PPAD-hard" (no definition of PPAD or of its reductions in the paper) → every search problem that reduces in polynomial time to WIN-LOSE-WSNE also reduces to APPROX-PACING; reason: by Chen et al. 2007 every PPAD problem reduces to WIN-LOSE-WSNE, so this yields the theorem for any reduction-based definition of PPAD-hardness, with no formal PPAD class
--   - reading: the PPAD-hardness of WIN-LOSE-WSNE (Chen et al. 2007), cited and not proved → it enters only through the hypothesis on Q; reason: the paper's conclusion rests on that citation and Lean has no proof of it
--   - encoding: rational games (p.3), computation unspecified → binary-encoded strings, Cook Turing machines, reductions correct for every answer, target instances with n ≥ 2 buyers; reason: the standard meaning of PPAD reductions; Definition 2 needs δ < 1 and the second bid needs two buyers, so n ≥ 2 only excludes undefined instances
--   - encoding: (α, x) real in Definition 2 (p.7), (x, y) real in Δn (p.30) → answers are binary codes of rational vectors satisfying the same real predicates; reason: answers are finite strings; this loses nothing: p.3 gives a rational exact pacing equilibrium of every rational game, and every rational bimatrix game has a rational Nash equilibrium
-- source:
--   Chen, Kroer, Kumar, The Complexity of Pacing for Second-Price Auctions, arXiv:2103.13969v2, Theorem 3, p.16 (proof in Appendix A, pp.30–34)

import Mathlib
import Definitions.Def_TetrisHard_Rows_Search
import Definitions.Def_CardinalMatching_SearchReduces
import Definitions.Def_PacingComplexity_WinLoseWSNE
import Definitions.Def_PacingComplexity_ApproxPacing

namespace PacingComplexity

open CardinalMatching

/-- **Theorem 3** (Chen, Kroer, Kumar, *The Complexity of Pacing for Second-Price Auctions*,
arXiv:2103.13969v2, §3.2, p.16; proof in Appendix A, pp.30–34): "The problem of computing a
(δ, γ)-approximate PE of an SPP game G = (n, m, (vij), (Bi)) with δ = γ = 1/n^7 is PPAD-hard."

Stated as a reduction closure: every search problem `Q` that reduces in polynomial time to
WIN-LOSE-WSNE (a `1/n`-well-supported Nash equilibrium of an `n × n` bimatrix game with costs in
`{0, 1}`) also reduces in polynomial time to APPROX-PACING_7 (a `(δ, γ)`-approximate pacing
equilibrium, `δ = γ = n^(−7)`, of a rational SPP game with `n ≥ 2` buyers).

**Formalization Note** The paper concludes from the PPAD-hardness of WIN-LOSE-WSNE (Chen et al.
2007, cited on p.34), which says that every PPAD problem satisfies the hypothesis, so this
statement gives Theorem 3 for any definition of PPAD-hardness by polynomial-time search
reductions from PPAD, without a formal PPAD class. Reductions are `SearchReduces` (Cook's Turing
machines, correct for every answer); encodings are binary. `n` in `δ = 1/n^7` is the number of
buyers of the pacing game. -/
theorem theorem_3 (Q : TetrisHard.Rows.SearchProblem) (hQ : SearchReduces Q WinLoseWSNE) :
    SearchReduces Q (ApproxPacing 7) := by sorry

end PacingComplexity
