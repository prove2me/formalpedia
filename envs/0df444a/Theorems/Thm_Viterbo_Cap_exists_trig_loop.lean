-- Prove2me | Theorems.Thm_Viterbo_Cap_exists_trig_loop
-- name    : Viterbo.Cap.exists_trig_loop
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-04T17:50:12.598829+00:00
-- url     : https://prove2.me/theorems/cdf6c75c-3d99-4742-ab62-efc62984b169
-- title:
--   A trigonometric loop w with ∫ h_L(−i ẇ)² < 4α·A(w) whenever α > c_EHZ(L)
-- statement:
--   Let $n\ge1$, $L\subseteq\mathbb R^{2n}$ a convex domain (`Viterbo.IsConvexDomain`) with $0$ in its interior, and $\alpha$ real with $c_{\rm EHZ}(L)<\alpha$ (in $[0,\infty]$, `Viterbo.cEHZ`). Then there are $D$ and $b:\mathbb Z\to\mathbb C^n$ such that
--   $$\int_0^1 h_{\Phi(L)}\big(-i\cdot\texttt{trigVel}\,D\,b\,(t)\big)^2\,dt<4\alpha\cdot\pi\sum_{m=-D}^{D}m\|b_m\|^2,$$
--   where $\Phi(L)\subseteq\mathbb C^n$ is the image of $L$ under $(q,p)\mapsto q+ip$ (`Viterbo.Capacities.Φ`) and $h$ is `supportFn`.
-- source:
--   Haim-Kislev, P. and Ostrover, Y., A counterexample to Viterbo's conjecture, Ann. of Math. 203 (2026) 603–622, https://doi.org/10.4007/annals.2026.203.2.5 (arXiv:2405.16513v3, whose page numbers are used), p. 2, a step in the proof of the capacity statement (Hofer–Zehnder argument, Hofer, H. and Zehnder, E., Symplectic Invariants and Hamiltonian Dynamics, Birkhäuser (1994), https://doi.org/10.1007/978-3-0348-8540-9, ch. 3)

import Mathlib
import Definitions.Def_Viterbo
import Definitions.Def_ViterboCap

open MeasureTheory Set Filter Topology OAI.SymmetricPolar
open scoped ENNReal ContDiff Pointwise NNReal
open OAI OAI.FourierPolynomial OAI.HamiltonianPeriodic

namespace Viterbo.Cap

theorem exists_trig_loop {n : ℕ} (hn : 1 ≤ n) {L : Set (Phase n)} (hL : IsConvexDomain L)
    (h0 : (0 : Phase n) ∈ interior L) {α : ℝ} (hα : cEHZ L < ENNReal.ofReal α) :
    ∃ (D : ℕ) (b : ℤ → Vector (Fin n)),
      ∫ t in (0 : ℝ)..1, supportFn (Capacities.Φ n '' L) (-(Complex.I • trigVel D b t)) ^ 2 <
        4 * α * trigAction D b := by
  sorry

end Viterbo.Cap
