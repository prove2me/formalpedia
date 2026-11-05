-- Prove2me | Theorems.Thm_Viterbo_Cap_engine
-- name    : Viterbo.Cap.engine
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-04T17:50:53.361711+00:00
-- url     : https://prove2.me/theorems/8353050c-f21c-4fba-a690-5b6a699cca5d
-- title:
--   Existence of a 1-periodic Hamiltonian orbit of positive action from the engine and cone hypotheses
-- statement:
--   Let $\kappa$ be a finite type and $H:\mathbb C^\kappa\to\mathbb R$ satisfy `Viterbo.Cap.EngineHyp H V C R γ₀` (see the bundle `Def_ViterboCap`), with $H\ge0$, $H=0$ on a neighbourhood of $0$, and `Viterbo.Cap.ConeHyp H`. Then there is $x:\mathbb R\to\mathbb C^\kappa$ with $x(1)=x(0)$, $\dot x(t)=i\,\nabla H(x(t))$ for every $t$, and positive `OAI.HamiltonianPeriodic.actionIntegral H x` $=\int_0^1\big(\tfrac12\langle\nabla H(x(t)),x(t)\rangle-H(x(t))\big)\,dt$.
-- source:
--   Haim-Kislev, P. and Ostrover, Y., A counterexample to Viterbo's conjecture, Ann. of Math. 203 (2026) 603–622, https://doi.org/10.4007/annals.2026.203.2.5 (arXiv:2405.16513v3, whose page numbers are used), p. 2, a step in the proof of the capacity statement (Hofer–Zehnder argument, Hofer, H. and Zehnder, E., Symplectic Invariants and Hamiltonian Dynamics, Birkhäuser (1994), https://doi.org/10.1007/978-3-0348-8540-9, ch. 3)

import Mathlib
import Definitions.Def_ViterboCap

open MeasureTheory Set Filter Topology OAI.SymmetricPolar
open scoped ENNReal ContDiff Pointwise NNReal
open OAI OAI.FourierPolynomial OAI.HamiltonianPeriodic

namespace Viterbo.Cap

theorem engine {κ : Type} [Fintype κ] [DecidableEq κ] {H : Vector κ → ℝ} {V : Vector κ → Vector κ} {C R γ₀ : ℝ}
    (hE : EngineHyp H V C R γ₀) (hH0 : ∀ z, 0 ≤ H z)
    (hflat : ∀ᶠ z in 𝓝 (0 : Vector κ), H z = 0) (hcone : ConeHyp H) :
    ∃ x : ℝ → Vector κ, x 1 = x 0 ∧ 0 < actionIntegral H x ∧
      ∀ t, HasDerivAt x (Complex.I • gradient H (x t)) t := by
  sorry

end Viterbo.Cap
