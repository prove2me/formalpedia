-- Prove2me | Theorems.Thm_QuasiStrictNE_Supplement_theorem_2
-- name    : QuasiStrictNE.Supplement.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:45:46.261622+00:00
-- url     : https://prove2.me/theorems/541e056d-88d4-4ed2-919c-949a2119d762
-- title:
--   Theorem 2, p.19 — for every fixed $n\ge3$, existence of a quasi-strict equilibrium is $\exists\mathbb R$-complete, even for zero-sum games
-- statement:
--   For every fixed $n \ge 3$, deciding whether an $n$-player game in strategic form with rational payoffs admits a quasi-strict Nash equilibrium is $\exists\mathbb R$-complete, even for zero-sum games. Precisely, for every $n \ge 3$ the following four statements hold:
--
--   1. $\mathrm{QSNEExists}_n \in \exists\mathbb R$;
--   2. $\mathrm{QSNEExists}_n$ is $\exists\mathbb R$-hard;
--   3. $\mathrm{QSNEExistsZS}_n \in \exists\mathbb R$;
--   4. $\mathrm{QSNEExistsZS}_n$ is $\exists\mathbb R$-hard.
--
--   Here $\mathrm{QSNEExists}_n$ is the set of codes of $n$-player rational games (every player with at least one action) that have a quasi-strict Nash equilibrium, $\mathrm{QSNEExistsZS}_n$ is its restriction to zero-sum games, and membership and hardness are by polynomial-time many-one reductions to and from the existential theory of the reals.
--
--   For two players a quasi-strict equilibrium always exists (Theorem 5). With three or more players it may fail to exist. Brandt and Fischer showed that deciding existence is NP-hard, and this theorem settles the exact complexity.
--
--   **Formalization Note** The number of players $n$ is fixed per language. The action counts and the full payoff table are the input, coded by `NGame.enc`. The $n$-player quasi-strict equilibrium is `NGame.IsQSNE`, which coincides with the base bimatrix definition for $n = 2$.
--
--   Differences from the source:
--   - encoding: an unspecified encoding of strategic-form games → the fixed self-delimiting code NGame.enc (n, the action counts, the payoff table in lexicographic order); reason: any two reasonable codes are polynomial-time interconvertible, so the problem is the same
--   - encoding: games with action sets A_i (implicitly nonempty) → codes with every k_i ≥ 1, strings that are not such codes outside the languages; reason: excludes only inputs that are not games
--   - encoding: ETR with polynomials with rational coefficients → the public ETRLanguage (constants 0 and 1, atoms = and <, connectives ¬ ∧ ∨); reason: the two versions are polynomial-time interreducible, so they define the same class ∃R and the same hardness
--   - reading: ∃R-membership and ∃R-hardness, machine model unstated → polynomial-time many-one reductions CookPvsNP.PolyReducible (Turing machines on bit strings) to and from ETR; reason: the standard definition of ∃R and of ∃R-hardness, the one the paper's own reductions realize
-- source:
--   Hansen & Nie, On Existence and Computational Complexity of Quasi-strict Equilibria, arXiv:2611.06350 (preprint, sha256 c265dace…), Theorem 2, p.19 (also p.3; proof pp.19–21)

import Mathlib
import Definitions.Def_QuasiStrictNE_Supplement_QSNEExists
import Definitions.Def_QuasiStrictNE_Supplement_QSNEExistsZS
import Definitions.Def_QuasiStrictNE_Supplement_ERComplete

set_option autoImplicit false

namespace QuasiStrictNE.Supplement

/-- **Theorem 2** (Hansen & Nie, *On Existence and Computational Complexity of Quasi-strict
Equilibria*, arXiv:2611.06350, Theorem 2, p.19 (also p.3): "For every fixed n ≥ 3, deciding whether an
n-player game in strategic form with rational payoffs admits a quasi-strict Nash equilibrium is
∃R-complete, even for zero-sum games").

For every fixed `n ≥ 3`, both the general-sum language `QSNEExists n` and the zero-sum language
`QSNEExistsZS n` are ∃R-complete: each is polynomial-time many-one reducible to ETR, and ETR is
polynomial-time many-one reducible to each.

**Formalization Note** ∃R-membership and ∃R-hardness are by polynomial-time many-one reductions
(`CookPvsNP.PolyReducible`) to and from the public `ETRLanguage` (see `ERComplete`). Games are in
strategic form, coded by `NGame.enc`; the number of players `n` is fixed per language. -/
theorem theorem_2 (n : ℕ) (hn : 3 ≤ n) :
    ERComplete (QSNEExists n) ∧ ERComplete (QSNEExistsZS n) := by sorry

end QuasiStrictNE.Supplement
