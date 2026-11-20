-- Prove2me | Theorems.Thm_RandomSizeStable_Stability_Supplement_theorem_2
-- name    : RandomSizeStable.Stability.Supplement.theorem_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-15T07:44:20.631684+00:00
-- url     : https://prove2.me/theorems/36853a52-6b32-4a25-92c0-ffc2a1419e94
-- title:
--   Theorem 2 — every fixed draw law has a profile where all random-size stable lotteries have distortion > 267/125
-- statement:
--   Let $D$ be any positive-integer-valued random variable, that is, any probability law on $\{1,2,3,\ldots\}$; infinite support and infinite mean are allowed. A **profile** consists of finitely many voters $V$ (at least one) and finitely many candidates $C$ (at least one), each voter $v$ reporting a strict ranking $\succ_v$ of $C$. A lottery $P$ on $C$ is a **random-size stable lottery** $\mathrm{RSL}_D$ if its masses are nonnegative and sum to one and, for every candidate $c$,
--   $$\Pr_v\big[c\succ_v P^D\big]\le\mathbb E\Big[\frac1{D+1}\Big]=\mu_D,$$
--   where $P^D$ is a tuple of $D$ independent draws from $P$ (with $D$ drawn first), $v$ is a uniformly random voter, and ties among copies of the same candidate are broken by independent uniform labels. For a **consistent pseudometric** $d$ on $V\cup C$ (that is, $a\succ_v b$ implies $d(v,a)\le d(v,b)$; distinct points may be at distance zero), write $\mathrm{SC}_d(c)=\mathbb E_v[d(v,c)]$ and $\mathrm{SC}_d(P)=\sum_cP(c)\,\mathrm{SC}_d(c)$. The **metric distortion** of $P$ on the profile is
--   $$\operatorname{dist}(P)=\sup_{d\text{ consistent}}\frac{\mathrm{SC}_d(P)}{\min_{c\in C}\mathrm{SC}_d(c)},\qquad 0/0=1,\quad z/0=+\infty\ (z>0).$$
--
--   The theorem states, for every fixed $D$:
--
--   1. there is a profile, depending only on $D$, on which every random-size stable lottery $P$ for $D$ satisfies
--   $$\operatorname{dist}(P)>\frac{267}{125}=2.136;$$
--   2. consequently, every randomized voting rule that, on every profile, returns a random-size stable lottery for this same $D$ has distortion strictly greater than $267/125$ on some profile.
--
--   Together with Theorem 1 (distortion at most $213609/100000$ for one fixed law $D^\star$), this places the best distortion attainable by random-size stable lottery rules with a fixed draw law in the interval $[2.136,\,2.13609]$: no choice of draw distribution can bring the guarantee down to $2.136$.
--
--   **Formalization Note** A profile is an election on `Fin n` voters and `Fin m` candidates with $n,m\ge1$, averaging uniformly over voters; relabeling covers every finite profile. "Distortion strictly greater than $B$" for $B=267/125\ge1$ is the negation of the published predicate `HasDistortionAtMost E P B`, i.e. there are a consistent pseudometric $d$ and a candidate $a$ with $\mathrm{SC}_d(P)>B\,\mathrm{SC}_d(a)$; this is equivalent to $\operatorname{dist}(P)>B$ including the zero-optimum conventions. Random-size stability is the published `IsStable D E P`, and a rule is the published ranking-only `VotingRule` family. The printed equality $267/125=2.136$ is kept as a conjunct.
--
--   Differences from the source:
--   - encoding: a profile on finite voter and candidate sets → an `Election (Fin n) (Fin m)` with 0 < n, 0 < m; reason: every finite nonempty profile is a relabeling of one on Fin n, Fin m, and the voter average is uniform as in the source
--   - encoding: metric distortion strictly greater than 267/125 with 0/0 = 1 and z/0 = +∞ → ¬ HasDistortionAtMost E P (267/125), i.e. some consistent pseudometric d and candidate a with lotteryCost d P > (267/125)·candCost d a; reason: for a bound B ≥ 1 the supremum exceeds B exactly when some consistent pseudometric exceeds it against some candidate, under the source's conventions
--   - encoding: a randomized voting rule of distortion strictly greater than 267/125 → a VotingRule family with some profile on which its lottery is not within 267/125; reason: the rule's distortion is the supremum over profiles, which exceeds the bound exactly when some profile does
-- source:
--   Nisarg Shah, Draw, Then Draw: The Metric Distortion of Random-Size Stable Lotteries, STOC 2027 submission #1342 (October 2026), p. 16 (also p. 5), Theorem 2; Definition 1 (p. 8) and Definition 3 (p. 10) for the notions used.

import Mathlib
import Definitions.Def_RandomSizeStable_Stability_Stability
import Definitions.Def_RandomSizeStable_Stability_VotingRule

set_option autoImplicit false

open MeasureTheory PctDistortion StableVotingDistortion

namespace RandomSizeStable.Stability.Supplement

/-- Theorem 2, pp.5 and 16: for every positive-integer draw law `D` (any PMF on ℕ+,
infinite support and infinite mean allowed), chosen BEFORE the profile, there is a finite
nonempty unweighted profile on which EVERY random-size stable lottery for `D` has metric
distortion strictly greater than 267/125 = 2.136; hence every rule that always returns an
RSL_D has distortion strictly greater than 267/125.
"Distortion strictly greater than B" (B ≥ 1, with the 0/0 = 1, z/0 = +∞ conventions of
Definition 1, p.8) is `¬ HasDistortionAtMost E P B`: some consistent pseudometric and
some candidate `a` with `cost(P) > B · cost(a)`. -/
theorem theorem_2 (D : PMF ℕ+) :
    (267 / 125 : ℝ) = 2.136 ∧
    (∃ (n m : ℕ) (_ : 0 < n) (_ : 0 < m) (E : Election (Fin n) (Fin m)),
      ∀ P : Fin m → ℝ, IsStable D E P → ¬ HasDistortionAtMost E P (267 / 125)) ∧
    (∀ R : VotingRule,
      (∀ (n m : ℕ) (hn : 0 < n) (hm : 0 < m) (E : Election (Fin n) (Fin m)),
        IsStable D E (R n m hn hm E).val) →
      ∃ (n m : ℕ) (hn : 0 < n) (hm : 0 < m) (E : Election (Fin n) (Fin m)),
        ¬ HasDistortionAtMost E (R n m hn hm E).val (267 / 125)) := by sorry

end RandomSizeStable.Stability.Supplement
