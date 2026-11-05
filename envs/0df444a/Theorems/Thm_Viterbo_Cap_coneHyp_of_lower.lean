-- Prove2me | Theorems.Thm_Viterbo_Cap_coneHyp_of_lower
-- name    : Viterbo.Cap.coneHyp_of_lower
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-04T17:50:36.222265+00:00
-- url     : https://prove2.me/theorems/d4284a3d-205a-4fa5-8b02-a5d118c507db
-- title:
--   The cone hypothesis from a lower bound H ≥ α·gauge_L² − C₀ and a trigonometric loop with ∫ h_L(−i ẇ)² < 4α·A(w)
-- statement:
--   Let $\kappa$ be a finite type, $H:\mathbb C^\kappa\to\mathbb R$ continuous, $L\subseteq\mathbb C^\kappa$ convex and bounded with $0$ in its interior, $\alpha>0$ and $C_0$ real with $\alpha\,\operatorname{gauge}_L(z)^2-C_0\le H(z)$ for all $z$. Suppose that for some $D$ and $b:\mathbb Z\to\mathbb C^\kappa$
--   $$\int_0^1 h_L\big(-i\,\dot w(t)\big)^2\,dt<4\alpha\cdot\pi\sum_{m=-D}^{D}m\|b_m\|^2,$$
--   where $w$ = `trigLoop D b`, $\dot w$ = `trigVel D b` and $h_L$ = `supportFn L`. Then `Viterbo.Cap.ConeHyp H` holds.
-- source:
--   Haim-Kislev, P. and Ostrover, Y., A counterexample to Viterbo's conjecture, Ann. of Math. 203 (2026) 603–622, https://doi.org/10.4007/annals.2026.203.2.5 (arXiv:2405.16513v3, whose page numbers are used), p. 2, a step in the proof of the capacity statement (Hofer–Zehnder argument, Hofer, H. and Zehnder, E., Symplectic Invariants and Hamiltonian Dynamics, Birkhäuser (1994), https://doi.org/10.1007/978-3-0348-8540-9, ch. 3)

import Mathlib
import Definitions.Def_ViterboCap

open MeasureTheory Set Filter Topology OAI.SymmetricPolar
open scoped ENNReal ContDiff Pointwise NNReal
open OAI OAI.FourierPolynomial OAI.HamiltonianPeriodic

namespace Viterbo.Cap

theorem coneHyp_of_lower {κ : Type} [Fintype κ] [DecidableEq κ] {H : Vector κ → ℝ} (hHc : Continuous H) {L : Set (Vector κ)}
    (hLc : Convex ℝ L) (hLb : Bornology.IsBounded L) (h0 : (0 : Vector κ) ∈ interior L)
    {α C₀ : ℝ} (hα : 0 < α) (hlow : ∀ z, α * gauge L z ^ 2 - C₀ ≤ H z)
    {D : ℕ} {b : ℤ → Vector κ}
    (hW : ∫ t in (0 : ℝ)..1, supportFn L (-(Complex.I • trigVel D b t)) ^ 2 <
      4 * α * trigAction D b) :
    ConeHyp H := by
  sorry

end Viterbo.Cap
