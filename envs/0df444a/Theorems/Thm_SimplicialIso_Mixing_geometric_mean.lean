-- Prove2me | Theorems.Thm_SimplicialIso_Mixing_geometric_mean
-- name    : SimplicialIso.Mixing.geometric_mean
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T07:20:24.72406+00:00
-- url     : https://prove2.me/theorems/f48c99d2-4a83-4359-9e52-ee48b9bfcaa5
-- title:
--   p. 18 — geometric mean over π ∈ Sym_{0..d} of ρ√(a_{π(0)}a_{π(d)})a_{π(1)}⋯a_{π(d−1)} is ρ(a_0⋯a_d)^{d/(d+1)}
-- statement:
--   Let $d\ge1$, let $a_0,\dots,a_d\ge0$ and $x\ge0$ be real numbers, and let $\rho\in\mathbb R$. If for every permutation $\pi$ of $\{0,\dots,d\}$
--   $$x\le\rho\sqrt{a_{\pi(0)}\,a_{\pi(d)}}\;a_{\pi(1)}\,a_{\pi(2)}\cdots a_{\pi(d-1)},$$
--   then
--   $$x\le\rho\,(a_0a_1\cdots a_d)^{\frac d{d+1}}.$$
--
--   This is the final step of the proof of the Mixing Lemma ("taking the geometric mean over all such $\pi$"), applied with $a_i=|A_i|$ and $x$ the discrepancy $\bigl||F|-\alpha\prod|A_i|/n\bigr|$.
--
--   **Formalization Note.** $x\ge0$ stands for the absolute value on the page; $d\ge1$ is needed (for $d=0$ the exponent is $0$ and the claim fails). The power is the real power `Real.rpow` of a nonnegative base.
-- source:
--   Parzanchevski, Rosenthal and Tessler, Isoperimetric inequalities in simplicial complexes, arXiv:1207.0638v3, §4.3, p. 18, 'Since A_0, . . . , A_d play the same role … Taking the geometric mean over all such π gives'

import Mathlib

namespace SimplicialIso.Mixing

open Finset
open scoped InnerProductSpace

/-- p. 18, the geometric-mean step: if a number `x ≥ 0` is at most
`ρ √(a_{π(0)} a_{π(d)}) a_{π(1)} ⋯ a_{π(d-1)}` for every permutation `π` of `{0, …, d}`, where
`a_0, …, a_d ≥ 0`, then `x ≤ ρ (a_0 a_1 ⋯ a_d)^{d/(d+1)}`. -/
theorem geometric_mean (d : ℕ) (hd : 1 ≤ d) (a : Fin (d + 1) → ℝ) (ha : ∀ i, 0 ≤ a i)
    (x ρ : ℝ) (hx : 0 ≤ x)
    (h : ∀ π : Equiv.Perm (Fin (d + 1)),
      x ≤ ρ * Real.sqrt (a (π 0) * a (π (Fin.last d))) *
        ∏ i ∈ univ.filter (fun i : Fin (d + 1) => i ≠ 0 ∧ i ≠ Fin.last d), a (π i)) :
    x ≤ ρ * (∏ i, a i) ^ ((d : ℝ) / (d + 1)) := by sorry

end SimplicialIso.Mixing
