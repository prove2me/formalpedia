-- Prove2me | Theorems.Thm_QBFBackdoor_round_count
-- name    : QBFBackdoor.round_count
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T11:32:25.014479+00:00
-- url     : https://prove2.me/theorems/1d09bbda-2b70-47b3-b21c-dd12a270946c
-- title:
--   §5.2 — the disjunct count of the balanced rounds and $O(\log(d_0+1))$ rounds
-- statement:
--   Let $g$ be the disjunct count after one balanced round ($g(5)=4$, and $g(d)=4\lfloor d/6\rfloor+(d\bmod 6)$ otherwise), and let $\mathrm{rounds}(d)$ be the number of rounds that bring $d$ disjuncts down to at most four. Then:
--
--   1. for every $d$, $\ g(d)\le \tfrac23 d+\tfrac53$;
--   2. for every $d\ge10$, $\ g(d)\le \tfrac56 d$;
--   3. for $5\le d\le 9$, $\ \mathrm{rounds}(d)\le 3$;
--   4. there is a constant $C$ with
--   $$
--   \mathrm{rounds}(d_0)\le C\,\lfloor\log_2(d_0+1)\rfloor\qquad\text{for every } d_0 .
--   $$
--
--   So the reduction to four disjuncts adds $O(\log(d_0+1))$ rounds, hence $O(\log(d_0+1))$ quantifier blocks.
--
--   Differences from the source:
--   - generalization: dt+1 = 4b + r ≤ (2/3)dt + 5/3 for an ordinary round → g(d) ≤ (2/3)d + 5/3 for every d, the padded round 5 ↦ 4 included; reason: the bound holds for every d; ordinary rounds are a special case
--   - encoding: the fractions 2/3, 5/3, 5/6 → cross-multiplied inequalities in ℕ (3·g(d) ≤ 2d + 5, 6·g(d) ≤ 5d); reason: the same inequalities
--   - encoding: O(log(d0+1)) rounds → ∃ C, rounds d0 ≤ C·⌊log₂(d0+1)⌋ for all d0; reason: ⌊log₂ x⌋ ≥ (log₂ x)/2 for x ≥ 2 and both sides vanish at d0 = 0, so the floor changes only the constant
--   - encoding: "If fewer than four remain, duplicate disjuncts to reach four" → rounds d = 0 for d ≤ 4; reason: padding up to four is not a squishing round
-- source:
--   Eriksson, Lagerkvist, Ordyniak, Osipov, Panolan, Rychlicki, Backdoors for Quantified Boolean Formulas, arXiv:2604.15927 (held version, sha256 3ea1662e…), §5.2, pp.25–26

import Mathlib
import Definitions.Def_QBFBackdoor_roundMap

namespace QBFBackdoor

/-- **The disjunct count of the balanced rounds.** Eriksson, Lagerkvist, Ordyniak, Osipov, Panolan, Rychlicki, *Backdoors for Quantified Boolean
Formulas*, arXiv:2604.15927 (held version, sha256 3ea1662e…), §5.2, pp.25–26: "If dt = 6b + r with
0 ≤ r < 6, an ordinary round gives dt+1 = 4b + r ≤ 2/3 dt + 5/3 … For dt ≥ 10, the first bound is
at most 5dt/6. Once 5 ≤ dt ≤ 9, at most three more rounds suffice, including the padded
five-disjunct case. … There are consequently O(log(d0+1)) rounds".

1. For every `d`, one round gives `roundMap d ≤ (2/3)d + 5/3` (the padded case `5 ↦ 4` included).
2. For `d ≥ 10`, `roundMap d ≤ (5/6)d`.
3. For `5 ≤ d ≤ 9`, at most three rounds bring `d` down to at most four.
4. There is a constant `C` with `rounds d₀ ≤ C · ⌊log₂(d₀ + 1)⌋` for every `d₀`.

**Formalization Note** Item 1 is stated for every `d`, including the padded round `5 ↦ 4` and `d ≤ 4`, where `roundMap d = d`. The inequalities are cross-multiplied in `ℕ`. `Nat.log 2` is the floor of
`log₂`; it is `≥ 1` for `d₀ ≥ 1`. The atom and size recursions of the same paragraph concern
the construction and are not part of this item. -/
theorem round_count :
    (∀ d, 3 * roundMap d ≤ 2 * d + 5) ∧
    (∀ d, 10 ≤ d → 6 * roundMap d ≤ 5 * d) ∧
    (∀ d, 5 ≤ d → d ≤ 9 → rounds d ≤ 3) ∧
    (∃ C : ℕ, ∀ d₀ : ℕ, rounds d₀ ≤ C * Nat.log 2 (d₀ + 1)) := by sorry

end QBFBackdoor
