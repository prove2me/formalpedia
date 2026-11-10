-- Prove2me | Theorems.Thm_RobersonCx_theorem_2
-- name    : RobersonCx.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:14:45.012396+00:00
-- url     : https://prove2.me/theorems/5da3677b-d680-447e-bc0c-8d1dd1403e82
-- title:
--   Theorem 2 — connected $H,H'$ with $H\in\mathrm{Cl}(\mathrm{Forb}_{\mathrm m}(H))$ and $H'\in\mathrm{Cl}(\mathrm{Forb}_{\mathrm{imm}}(H'))$
-- statement:
--   There exist finite connected graphs $H$ and $H'$ such that
--   $$H\in\mathrm{Cl}\big(\mathrm{Forb}_{\mathrm m}(H)\big)\qquad\text{and}\qquad H'\in\mathrm{Cl}\big(\mathrm{Forb}_{\mathrm{imm}}(H')\big),$$
--   where $\mathrm{Forb}_{\mathrm m}(H)$ is the class of graphs not containing $H$ as a minor and $\mathrm{Forb}_{\mathrm{imm}}(H')$ the class of graphs in which $H'$ does not (weakly) immerse.
--
--   Since $\mathrm{Forb}_{\mathrm m}(H)$ is closed under minors and disjoint unions but does not contain $H$, this refutes the Strong Roberson Conjecture; the second membership refutes its immersion analogue. The paper's witnesses are $D^{(5)}_{91}$ and $B^{(5)}_{91}$.
--
--   Differences from the source: none.
-- source:
--   Kristjánsson, Counterexamples to the Strong Roberson Conjecture, arXiv:2610.03550 (version of 2 November 2026, sha256 1b70a7c6…), Theorem 2, p.3 (PDF p.5)

import Mathlib
import Definitions.Def_RobersonCx_InCl
import Definitions.Def_RobersonCx_ForbMinor

set_option autoImplicit false

namespace RobersonCx

/-- Theorem 2 (Kristjánsson, *Counterexamples to the Strong Roberson Conjecture*, arXiv:2610.03550 (version of 2 November 2026, sha256 1b70a7c6…), §1.1, p.3 (PDF p.5)), the main result. There exist connected graphs `H` and `H′` such that
`H ∈ Cl(Forb_m(H))` and `H′ ∈ Cl(Forb_imm(H′))`.

**Formalization Note** `H`, `H′` are simple graphs on finite types in `Type`; `Cl` quantifies its targets over
every finite graph (`InCl`); `Forb_m` uses minors in the sense of Definition 12 and `Forb_imm` the weak immersion
of Definition 3. The witnesses are not named (the paper gives `D^(5)_91` and `B^(5)_91`). -/
theorem theorem_2 :
    ∃ (V : Type) (_ : Finite V) (H : SimpleGraph V) (V' : Type) (_ : Finite V') (H' : SimpleGraph V'),
      H.Connected ∧ InCl (ForbMinor H) H ∧ H'.Connected ∧ InCl (ForbImm H') H' := by sorry

end RobersonCx
