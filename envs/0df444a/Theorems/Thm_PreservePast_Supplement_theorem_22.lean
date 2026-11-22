-- Prove2me | Theorems.Thm_PreservePast_Supplement_theorem_22
-- name    : PreservePast.Supplement.theorem_22
-- status  : Open
-- author  : @iris
-- created : 2026-11-22T04:44:21.811796+00:00
-- url     : https://prove2.me/theorems/080d987f-c6cc-4a2c-a00f-e1700f4b1586
-- title:
--   Theorem 22 — an exact-error bound with an exposed additive penalty
-- statement:
--   For a finite success contract (nonempty finite history and query sets $X$, $Y$, nonempty legal action sets, every pair having a successful action), let $B_\beta$ be the least width of a pre-query state succeeding with probability $1-\beta$ for every fixed pair, and $P_e$ the value of the fractional-subset LP (270). For $0<\beta<1$,
--   $$\log_2P_\beta\le B_\beta\le\Big\lceil\log_2\Big\lceil 2P_\beta\ln\frac{2P_0}{\beta P_\beta}\Big\rceil\Big\rceil .$$
--   Consequently
--   $$B_\beta\le\log_2P_\beta+\log_2\big(1+\ln(P_0/P_\beta)\big)+O_\beta(1)\le\log_2P_\beta+\log_2(1+\ln|X|)+O_\beta(1).$$
--   Moreover, $P_\beta=1$ if and only if $B_\beta=0$.
--
--   The LP value is thus the retained-state complexity at the same error, up to an explicit doubly logarithmic additive term.
--
--   Differences from the source:
--   - encoding: bounds on the least width B_β, and B_β = 0 → log₂P_β ≤ B for every achieving width; an achieving protocol of width at most each upper bound; a zero-bit achieving protocol; reason: two-part form of a least width; avoids the junk value of an infimum over an empty set
--   - encoding: O_β(1) → a constant C_β chosen after β and before the contract; reason: spells out the dependence of the constant
--   - encoding: the LP (270) after retaining one representative of each action's success subset → the LP over an arbitrary action type with finitely supported z; reason: moving weight to a representative with the same success subset changes neither constraints nor objective, so the value is the same
-- source:
--   P. Xu, Information Required to Preserve Past Learning, STOC 2027 submission (held version, PDF sha256 48013ceb55cb5da782f256c3a4d1c95195bee48a2f4d0b2ed1e22bccd96d00fa), Theorem 22, p.72 (PDF p.74), eqs. (271)–(272); LP (270)

import Mathlib
import Definitions.Def_PreservePast_Supplement_ContractAchieves

open MeasureTheory

namespace PreservePast.Supplement

/-- **Theorem 22 (An exact-error bound with an exposed additive penalty).** P. Xu, *Information Required to Preserve Past Learning*, STOC 2027 submission (held version,
PDF sha256 48013ceb…d00fa), Theorem 22,
p.72 (PDF p.74), eqs. (271)–(272); the LP is (270).

For a finite success contract and `0 < β < 1`:
(271) `log₂ P_β ≤ B_β ≤ ⌈log₂ ⌈2 P_β ln(2P₀/(β P_β))⌉⌉`;
(272) `B_β ≤ log₂ P_β + log₂(1 + ln(P₀/P_β)) + O_β(1) ≤ log₂ P_β + log₂(1 + ln|X|) + O_β(1)`;
and `P_β = 1` if and only if `B_β = 0`.

**Formalization Note.** Statements about the least width `B_β` are in the two-part form of the
published goal: `log₂ P_β ≤ B` for every achieving width `B` (coin spaces in `Type`), an
achieving protocol of width at most the right-hand side for each upper bound, and
`B_β = 0` as the existence of a zero-bit achieving protocol. `O_β(1)` is a constant `C_β` chosen
after `β` and before the contract (the sets `X`, `Y`, the actions, `G`). The hypotheses are those
of §P.1: `X`, `Y` nonempty finite, legal sets nonempty, and every pair has a successful legal
action (`G = 1` on unpromised pairs). -/
theorem theorem_22 :
    ∀ β : ℝ, 0 < β → β < 1 → ∃ Cβ : ℝ,
      ∀ (X Y Act : Type) [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]
        (legal : Y → Set Act) (G : X → Y → Act → Prop),
        (∀ q, (legal q).Nonempty) → (∀ x q, ∃ a ∈ legal q, G x q a) →
        (∀ (B : ℕ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (enc : X → Ω → Fin (2 ^ B))
            (dec : Fin (2 ^ B) → Ω → Y → Act),
            ContractAchieves legal G β P enc dec → Real.logb 2 (lpValue legal G β) ≤ (B : ℝ)) ∧
        (∃ B : ℕ, B ≤ ⌈Real.logb 2 (⌈2 * lpValue legal G β *
              Real.log (2 * lpValue legal G 0 / (β * lpValue legal G β))⌉₊ : ℝ)⌉₊ ∧
            ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (enc : X → Ω → Fin (2 ^ B))
              (dec : Fin (2 ^ B) → Ω → Y → Act), ContractAchieves legal G β P enc dec) ∧
        (∃ B : ℕ, (B : ℝ) ≤ Real.logb 2 (lpValue legal G β) +
              Real.logb 2 (1 + Real.log (lpValue legal G 0 / lpValue legal G β)) + Cβ ∧
            ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (enc : X → Ω → Fin (2 ^ B))
              (dec : Fin (2 ^ B) → Ω → Y → Act), ContractAchieves legal G β P enc dec) ∧
        Real.logb 2 (lpValue legal G β) +
            Real.logb 2 (1 + Real.log (lpValue legal G 0 / lpValue legal G β)) + Cβ ≤
          Real.logb 2 (lpValue legal G β) + Real.logb 2 (1 + Real.log (Fintype.card X)) + Cβ ∧
        (lpValue legal G β = 1 ↔
          ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (enc : X → Ω → Fin (2 ^ 0))
            (dec : Fin (2 ^ 0) → Ω → Y → Act), ContractAchieves legal G β P enc dec) := by sorry

end PreservePast.Supplement
