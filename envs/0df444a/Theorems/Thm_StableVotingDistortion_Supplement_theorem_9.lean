-- Prove2me | Theorems.Thm_StableVotingDistortion_Supplement_theorem_9
-- name    : StableVotingDistortion.Supplement.theorem_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T01:59:20.036016+00:00
-- url     : https://prove2.me/theorems/9f02b765-3713-4947-a9ca-286ec1a91078
-- title:
--   Theorem 9 — $2$-, $3$-, $4$-tournament rules have metric distortion at least $3$, $7/3$, $11/5$
-- statement:
--   The metric distortion of any $2$-, $3$-, or $4$-tournament rule is at least $3$, $7/3$, or $11/5$, respectively.
--
--   That is, for $(\ell,x)\in\{(2,3),(3,7/3),(4,11/5)\}$: if a randomized voting rule $f$ returns the same lottery on any two elections with the same candidates and the same number of voters that have, for every set $S$ of at most $\ell$ candidates, the same fraction of voters ordering $S$ in each way, then for every $B<x$ there are an election $E$, a pseudometric $d$ consistent with $E$ and a candidate $a$ with $\mathrm{cost}_d(f(E))>B\cdot\mathrm{cost}_d(a)$.
--
--   With Theorem 6, stable $2$-lotteries (which are $3$-tournament rules) are optimal among $3$-tournament rules.
--
--   **Formalization Note** Rules, $\ell$-tournament rules and "distortion at least $x$" are as in the definition `IsTournamentRule`.
--
--   Differences from the source:
--
--   - encoding: a randomized voting rule → RandomSizeStable.Stability.VotingRule, one family on every Election (Fin n) (Fin m) with n, m > 0, returning a lottery; reason: every finite nonempty election is one of these up to relabeling
--   - generalization: an ℓ-tournament rule only sees the aggregate rankings of tuples of ℓ candidates (p.40: the distribution of the voters' orderings of every S with |S| ≤ ℓ) → IsTournamentRule ℓ f: f gives the same lottery on two elections with the same candidates and the same number of voters whenever their voter fractions agree for every ordering of every set of at most ℓ candidates; reason: every rule that sees only the distribution (fractions) or only the counts satisfies this, so the Lean class contains the paper's under either reading and the theorem specializes to the source; the proof (Corollary 13, p.41) compares an election only with its relabelings, which have the same number of voters
--   - encoding: metric distortion at least x → RuleDistortionAtLeast f x: for every B < x some election has a consistent pseudometric and a candidate violating cost_d(f(E)) ≤ B·cost_d(a); reason: the definition of distortion(f) on p.6 as a supremum, with the base mission inequality form
-- source:
--   Cai, Frank, Hastings, Ramakrishnan, Wang, Ye, Stable Voting Rules on the Edge of Optimal Metric Distortion, arXiv:2609.08259 (held version, sha256 cfdd5f3d…), Theorem 9, p.40; §1, p.4; Appendix B, p.40 and footnote 15

import Mathlib
import Definitions.Def_RandomSizeStable_Stability_VotingRule
import Definitions.Def_StableVotingDistortion_Supplement_IsTournamentRule

set_option autoImplicit false

namespace StableVotingDistortion.Supplement

/-- **Theorem 9.** The metric distortion of any `2`-, `3`-, or `4`-tournament rule is at least `3`, `7/3`, or
`11/5`, respectively.

Cai et al., arXiv:2609.08259 (held version, sha256 cfdd5f3d…), Theorem 9, p.40: "The metric distortion of any 2-,
3-, or 4-tournament rule is at least 3, 7/3, or 11/5, respectively."

**Formalization Note.** A rule is the platform's `VotingRule` (one family on every `Election (Fin n) (Fin m)`);
an `ℓ`-tournament rule is `IsTournamentRule ℓ` (its output depends only on the voters' ordering fractions on the
sets of at most `ℓ` candidates); "distortion at least `x`" is `RuleDistortionAtLeast f x`: no `B < x` bounds the
distortion of `f` on every election. The sentence "Consequently, …" after the theorem is not part of it. -/
theorem theorem_9 :
    (∀ f : RandomSizeStable.Stability.VotingRule, IsTournamentRule 2 f → RuleDistortionAtLeast f 3) ∧
    (∀ f : RandomSizeStable.Stability.VotingRule, IsTournamentRule 3 f → RuleDistortionAtLeast f (7 / 3)) ∧
    (∀ f : RandomSizeStable.Stability.VotingRule, IsTournamentRule 4 f → RuleDistortionAtLeast f (11 / 5)) := by sorry

end StableVotingDistortion.Supplement
