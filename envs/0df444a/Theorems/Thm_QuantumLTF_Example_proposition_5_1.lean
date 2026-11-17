-- Prove2me | Theorems.Thm_QuantumLTF_Example_proposition_5_1
-- name    : QuantumLTF.Example.proposition_5_1
-- status  : Open
-- author  : @stockfish-soup
-- created : 2026-11-16T17:54:35.230788+00:00
-- url     : https://prove2.me/theorems/ecf5c09e-ab51-448a-9ec8-8eb978d26e58
-- title:
--   Proposition 5.1 — halfspace-boundary discretization error
-- statement:
--   For a unit normal $w$, coordinatewise downward rounding to the finite Gaussian grid satisfies $\int_{[-L,L]^n}|f_w(x)-f_w(\bar x)|^2d\gamma_n(x)\le4\sqrt{8n/M}$.
-- source:
--   Krivcenko, Nguyen, de Wolf, STOC 2027 submission #347, Proposition 5.1, p.57 (PDF p.58).

import Mathlib
import Definitions.Def_QuantumLTF_Membership_ltf
import Definitions.Def_QuantumLTF_Example_HermiteModel

namespace QuantumLTF.Example

open MeasureTheory ProbabilityTheory QuantumLTF.Membership

theorem proposition_5_1 : ∀ n M : ℕ, 1≤n → 1≤M → ∀ w : EuclideanSpace ℝ (Fin n), ‖w‖=1 → let L:=gridRadius M; ∫ x in {x : EuclideanSpace ℝ (Fin n) | ∀ i, -L≤x i ∧ x i≤L}, (((ltf w 0 x-ltf w 0 (roundVec M x):ℤ):ℝ)^2) ∂(stdGaussian (EuclideanSpace ℝ (Fin n))) ≤ 4*Real.sqrt (8*n/M) := by sorry

end QuantumLTF.Example
