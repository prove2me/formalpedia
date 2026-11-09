-- Prove2me | Theorems.Thm_SemAC02_proposition_8_3_lift_unsat
-- name    : SemAC02.proposition_8_3_lift_unsat
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T11:29:38.571522+00:00
-- url     : https://prove2.me/theorems/4f727e6a-4e05-4454-a9b6-7273ec85d93f
-- title:
--   Proposition 8.3 — lifting preserves unsatisfiability
-- statement:
--   Let $g$ be a gadget as in §8.1 and $F_n$ a CNF. If $F_n$ is unsatisfiable, then $\mathrm{Lift}_g(F_n)$ is unsatisfiable: no assignment to the $nm$ lifted variables satisfies every circuit $A_{C,\alpha}$ of $\mathrm{Lift}_g(F_n)$.
--
--   Unsatisfiability of the lift is what makes refutations of $\mathrm{Lift}_g(F_n)$ exist at all.
--
--   Differences from the source:
--   - generalization: base CNF of §8.1 with clauses of 1 ≤ |I| ≤ w₀ literals → any CNF F (empty clauses and any width allowed); reason: an empty clause lifts to the empty OR, which no assignment satisfies, so the conclusion still holds; the source's CNFs are a special case
--   - encoding: the standing assumptions of §8.1 on d and g → 2 ≤ d and IsGadget d g (normal form included); reason: the paper's circuits are in normal form by definition
-- source:
--   Alekseev, Gryaznov, Itsykson, Pitassi, Robere, Tzameret, Hard Instances for Strong Semantic Proof Systems: CNFs for Depth-Four PC and Deep Instances for AC0[2]-Frege, manuscript (STOC 2027 submission, sha256 c228d68b89b45b5c6c547aa994f7d1799441bb22b2a85e36c6cd400bea8cdb6a), Proposition 8.3, p.63 (PDF p.65)

import Mathlib
import Definitions.Def_SemAC02_Circ
import Definitions.Def_SemAC02_IsGadget
import Definitions.Def_SemAC02_lift
import Definitions.Def_LiftSAParity_CNF

namespace SemAC02

/-- **Proposition 8.3** (Alekseev–Gryaznov–Itsykson–Pitassi–Robere–Tzameret, *Hard Instances for Strong Semantic Proof
Systems*, manuscript (STOC 2027 submission), Proposition 8.3, p.63): for a gadget `g` as in §8.1,
if `F_n` is unsatisfiable, then `Lift_g(F_n)` is unsatisfiable: no assignment to the lifted
variables satisfies every circuit of `Lift_g(F_n)`.

**Formalization Note** The standing assumptions of §8.1 on `g` are `IsGadget d g` with
`d ≥ 2`. -/
theorem proposition_8_3_lift_unsat {d n m : ℕ} (hd : 2 ≤ d) (g : Circ (Fin m)) (hg : IsGadget d g)
    (F : LiftSAParity.CNF (Fin n)) (hF : ¬ LiftSAParity.Satisfiable F) :
    ¬ ∃ X : Fin n × Fin m → Bool, ∀ A ∈ lift g F, A.eval X = true := by sorry

end SemAC02
