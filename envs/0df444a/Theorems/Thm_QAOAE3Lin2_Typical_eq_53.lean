-- Prove2me | Theorems.Thm_QAOAE3Lin2_Typical_eq_53
-- name    : QAOAE3Lin2.Typical.eq_53
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T10:58:00.040062+00:00
-- url     : https://prove2.me/theorems/dbb61361-d790-406a-b74a-ce273084848c
-- title:
--   Section III, (51)–(53), p. 10 — at γ = 1/(√3 D^{1/2}), D^{1/2} sin γ cos^{3D} γ → 1/√(3e) as D → ∞
-- statement:
--   For a natural number $D$ put $\gamma_D=1/\sqrt{3D}$, the choice $g=1/\sqrt3$ in (51). Then
--   $$\lim_{D\to\infty} D^{1/2}\,\sin\gamma_D\,\cos^{3D}\gamma_D=\frac1{\sqrt{3e}} .$$
--   Consequently, at this angle the lower bound of (50) is $(1+o(1))\,\dfrac{m}{2\sqrt{3e}\,D^{1/2}}$, which is (53).
--
--   This is the "for large $D$" optimization of (51)–(53), stated as an exact limit.
--
--   **Formalization Note** The paper's (54), $\big(\tfrac12+\tfrac1{2\sqrt{3e}D^{1/2}}\big)m$, is not stated as a finite-$D$ inequality: $\sin\gamma\cos^{3D}\gamma<1/\sqrt{3eD}$ for every $D\ge1$ (for instance at $D=100$, $0.034989<0.035016$), so that inequality is false. The limit is the exact content of (52)–(53). The value at $D=0$ (where Lean's $1/0=0$) is irrelevant to the limit.
-- source:
--   Farhi, Goldstone, Gutmann, A Quantum Approximate Optimization Algorithm Applied to a Bounded Occurrence Constraint Problem, arXiv:1412.6062v2, p. 10, Section III, (51)–(53)

import Mathlib

namespace QAOAE3Lin2.Typical

/-- (51)–(53), p. 10, as a limit: at `γ = 1/(√3 D^{1/2})`, `D^{1/2} sin γ cos^{3D} γ → 1/√(3e)` as
`D → ∞`, so (50)'s lower bound is `(1 + o(1)) m/(2√(3e) D^{1/2})`. -/
theorem eq_53 :
    Filter.Tendsto
      (fun D : ℕ => Real.sqrt D *
        (Real.sin (1 / Real.sqrt (3 * D)) * Real.cos (1 / Real.sqrt (3 * D)) ^ (3 * D)))
      Filter.atTop (nhds (1 / Real.sqrt (3 * Real.exp 1))) := by sorry

end QAOAE3Lin2.Typical
