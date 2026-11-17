-- Prove2me | Theorems.Thm_SybilClinch_Supplement_theorem_7_1
-- name    : SybilClinch.Supplement.theorem_7_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T04:20:42.388513+00:00
-- url     : https://prove2.me/theorems/b8d19e92-3144-4289-8f53-345839a71807
-- title:
--   Theorem 7.1 — impossibility with affordable budget overreporting
-- statement:
--   Let an admissible AMM have arbitrary positive initial reserves $(x_0,y_0)$ and the constant-product curve
--
--   $$
--   \varphi(x)=\frac{x_0y_0}{x}\qquad(x>0).
--   $$
--
--   There is no deterministic mechanism defined on every profile of two finite eligible sell-$Y$ users that simultaneously satisfies:
--
--   1. individual rationality (Definition 2.3);
--   2. exact settlement against the pool (Definition 2.2);
--   3. both clauses of weak Pareto optimality (Definition 2.7); and
--   4. incentive compatibility against every single-identity finite eligible value and budget misreport, including a declared budget above the true budget whenever the deviation's realized payment is at most that true budget.
--
--   The impossibility requires neither symmetry, Sybil resistance nor protection from opposite-direction deviations.
--
--   Differences from the source:
--   - encoding: a deterministic mechanism on profiles of two sell-$Y$ users → a function `(Fin 2 → Report) → Fin 2 → Fill`, embedded under labels $0,1$ into the published settlement, individual-rationality and weak-Pareto predicates; reason: `Fin 2` is exactly the fixed two-user domain and functionhood is determinism
--   - encoding: an arbitrary positive-reserve constant-product AMM, normalized only inside the proof → an admissible AMM satisfying $\varphi(x)=x_0y_0/x$ for every $x>0$, with no normalization of $x_0$ or $y_0$; reason: this states the theorem before its proof-only rescaling
--   - encoding: an affordable budget overreport → the deviating fill's realized sell-$Y$ payment is at most the truthful report's budget, while the declared deviating budget is otherwise unrestricted; reason: this is the enlarged strategy space defined immediately before Theorem 7.1
-- source:
--   Zhang, Li, Shi, Zhang, Xia, Han, Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design, arXiv:2610.36629 (held copy sha256 93c5d05b…), Theorem 7.1, printed pp.34–35 (PDF pp.36–37), with the enlarged strategy space on printed p.34

import Mathlib
import Definitions.Def_SybilClinch_AdmissibleAMM_y0
import Definitions.Def_SybilClinch_Report_Valid
import Definitions.Def_SybilClinch_Fill
import Definitions.Def_SybilClinch_IsEligible
import Definitions.Def_SybilClinch_ExactSettle
import Definitions.Def_SybilClinch_IndivRational
import Definitions.Def_SybilClinch_WeakPO

set_option autoImplicit false

open Filter Topology Set

namespace SybilClinch

namespace Supplement

/-- Zhang, Li, Shi, Zhang, Xia, Han, *Sybil-Proofness of Generalized Adaptive Clinching and
Implications for Blockchain Mechanism Design*, arXiv:2610.36629 (held copy sha256
93c5d05b05cc8b80b5bb5c0ac677b9642e119277d82de797234b0242f7c5021c), Theorem 7.1
(Budget-overreporting impossibility), printed pp.34–35 (PDF pp.36–37).

For an arbitrary positive-reserve constant-product AMM there is no deterministic mechanism on
every profile of two finite eligible sell-`Y` users that is simultaneously exact-settlement
feasible, individually rational, weakly Pareto optimal in both clauses of Definition 2.7, and
incentive compatible against every single-identity eligible value/budget misreport whose realized
payment is affordable under the user's true budget.

**Formalization Note.** A deterministic mechanism is a function from the two reports (`Fin 2`) to
the two fills. The local `liftRep` and `liftFill` merely embed this fixed two-user domain into the
published predicates, whose labels are `0` and `1`; values and budgets are real and hence finite.
The constant-product identity is imposed for every positive reserve `x`, without the proof's
normalization `x₀=y₀=1`. -/
theorem theorem_7_1 (A : AdmissibleAMM)
    (hprod : ∀ x : ℝ, 0 < x → A.φ x = A.x0 * A.y0 / x) :
    ¬ ∃ mech : (Fin 2 → Report) → Fin 2 → Fill,
      let liftRep : (Fin 2 → Report) → ℕ → Report := fun r n =>
        if h : n < 2 then r ⟨n, h⟩ else { dir := Dir.sellY, val := 0, bud := 0 }
      let liftFill : (Fin 2 → Fill) → ℕ → Fill := fun f n =>
        if h : n < 2 then f ⟨n, h⟩ else { sold := 0, recv := 0 }
      (∀ r : Fin 2 → Report,
          (∀ i, (r i).Valid ∧ (r i).dir = Dir.sellY ∧ IsEligible A (r i)) →
          ExactSettle A (Finset.range 2) (liftRep r) (liftFill (mech r))) ∧
      (∀ r : Fin 2 → Report,
          (∀ i, (r i).Valid ∧ (r i).dir = Dir.sellY ∧ IsEligible A (r i)) →
          IndivRational (Finset.range 2) (liftRep r) (liftFill (mech r))) ∧
      (∀ r : Fin 2 → Report,
          (∀ i, (r i).Valid ∧ (r i).dir = Dir.sellY ∧ IsEligible A (r i)) →
          WeakPO A (Finset.range 2) (liftRep r) (liftFill (mech r))) ∧
      ∀ (r : Fin 2 → Report),
        (∀ i, (r i).Valid ∧ (r i).dir = Dir.sellY ∧ IsEligible A (r i)) →
        ∀ (i : Fin 2) (dev : Report), dev.Valid → dev.dir = Dir.sellY → IsEligible A dev →
          (mech (Function.update r i dev) i).sold ≤ (r i).bud →
          (r i).val * (mech (Function.update r i dev) i).recv -
              (mech (Function.update r i dev) i).sold ≤
            (r i).val * (mech r i).recv - (mech r i).sold := by sorry

end Supplement

end SybilClinch
