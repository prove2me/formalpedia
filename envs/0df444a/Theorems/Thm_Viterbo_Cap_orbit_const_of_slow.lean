-- Prove2me | Theorems.Thm_Viterbo_Cap_orbit_const_of_slow
-- name    : Viterbo.Cap.orbit_const_of_slow
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-04T17:50:18.644889+00:00
-- url     : https://prove2.me/theorems/9917057f-786d-4b2d-96d8-fe4f92a50197
-- title:
--   A slow profile of a mollified gauge of K has only constant 1-periodic Hamiltonian orbits
-- statement:
--   Let $n\ge1$ and $K\subseteq\mathbb C^n$ with `Body K r` (convex, bounded, containing the open $r$-ball about $0$) and $\Psi(K)$ a convex domain, $\Psi(w)=(\operatorname{Re}w,\operatorname{Im}w)$. Let $\varphi$ be a smooth bump about $0$ of outer radius $\varepsilon:=$ `φ.rOut` $<r$, $Q$ = `mollQ K φ`, and $f:\mathbb R\to\mathbb R$ smooth with $f'\ge0$, $f'(s)=0$ for $s\le(2\varepsilon/r)^2$, and
--   $$f'(s)\,s<\big(\sqrt s-\varepsilon/r\big)^2\,c_{\rm EHZ}(\Psi(K))\ \ (\text{as a real number, `toReal`})\quad\text{whenever }f'(s)>0.$$
--   If $y:\mathbb R\to\mathbb C^n$ satisfies $\dot y(t)=i\,\nabla(f\circ Q)(y(t))$ for all $t$ and $y(1)=y(0)$, then $y$ is constant.
-- source:
--   Haim-Kislev, P. and Ostrover, Y., A counterexample to Viterbo's conjecture, Ann. of Math. 203 (2026) 603–622, https://doi.org/10.4007/annals.2026.203.2.5 (arXiv:2405.16513v3, whose page numbers are used), p. 2, a step in the proof of the capacity statement (Hofer–Zehnder argument, Hofer, H. and Zehnder, E., Symplectic Invariants and Hamiltonian Dynamics, Birkhäuser (1994), https://doi.org/10.1007/978-3-0348-8540-9, ch. 3)

import Mathlib
import Definitions.Def_Viterbo
import Definitions.Def_ViterboCap

open MeasureTheory Set Filter Topology OAI.SymmetricPolar
open scoped ENNReal ContDiff Pointwise NNReal
open OAI OAI.FourierPolynomial OAI.HamiltonianPeriodic

namespace Viterbo.Cap

theorem orbit_const_of_slow {n : ℕ} (hn : 1 ≤ n) {K : Set (Vector (Fin n))} {r : ℝ}
    (hK : Body K r) (hKd : IsConvexDomain (Capacities.Ψ n '' K))
    (φ : ContDiffBump (0 : Vector (Fin n))) (hφ : φ.rOut < r)
    {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hf0 : ∀ s, 0 ≤ deriv f s)
    (hfa : ∀ s, s ≤ (2 * φ.rOut / r) ^ 2 → deriv f s = 0)
    (hslow : ∀ s, 0 < deriv f s →
      deriv f s * s < (Real.sqrt s - φ.rOut / r) ^ 2 * (cEHZ (Capacities.Ψ n '' K)).toReal)
    {y : ℝ → Vector (Fin n)}
    (hy : ∀ t, HasDerivAt y (Complex.I • gradient (fun w => f (mollQ K φ w)) (y t)) t)
    (hp : y 1 = y 0) : ∀ t, y t = y 0 := by
  sorry

end Viterbo.Cap
