-- Prove2me | Theorems.Thm_QuantumEcon_Duopoly_corollary_1
-- name    : QuantumEcon.Duopoly.corollary_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T09:41:59.563724+00:00
-- url     : https://prove2.me/theorems/91a5187b-c37d-43d5-b411-0778b1b7f864
-- title:
--   Corollary 1: quantum monopoly without product differentiation
-- statement:
--   With no investment, identical offerings ($\gamma=1$), and $1<c<a<c^2$, the unique constrained Cournot equilibrium has classical quantity zero and quantum quantity $(a-c)/2$. The classical unit cost exceeds demand while the quantum firm can still sell.
--
--   This statement is a source-indexed target for the two-stage model.
-- source:
--   Bova, Goldfarb, Melko, Quantum Economic Advantage, NBER Working Paper No. 29724 (February 2022), PDF p. 17, Corollary 1

import Definitions.Def_QuantumEcon_Duopoly_Setting

set_option autoImplicit false

namespace QuantumEcon.Duopoly

/-- Bova, Goldfarb, Melko, Quantum Economic Advantage, NBER Working Paper No. 29724
(February 2022), PDF p. 17, Corollary 1, in the no-investment §3.1 model.
Formalization Note: `γ = 1`, and `a < c²` replaces the main model's standing
`c² < a`; `a > c` makes the quantum monopolist's output positive. -/
theorem corollary_1 (a c q₁ q₂ : ℝ) (hc : 1 < c) (hca : c < a) (hac : a < c ^ 2) :
    SupplierAudit.Competition.IsCournotNash 1 a c a (c ^ 2) q₁ q₂ ↔
      q₁ = (a - c) / 2 ∧ q₂ = 0 := by sorry

end QuantumEcon.Duopoly
