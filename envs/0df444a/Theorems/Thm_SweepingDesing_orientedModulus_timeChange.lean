-- Prove2me | Theorems.Thm_SweepingDesing_orientedModulus_timeChange
-- name    : SweepingDesing.orientedModulus_timeChange
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:16:05.627555+00:00
-- url     : https://prove2.me/theorems/77948102-52e2-432b-8edb-f25b3fb7a3a3
-- title:
--   §4.2, p.15 — time rescaling multiplies the oriented modulus by $\Psi'(r)$
-- statement:
--   Let $S:\mathbb R\rightrightarrows\mathbb R^n$ be any set-valued map, $r\in\mathbb R$, and $\Psi:\mathbb R\to\mathbb R$ continuously differentiable on a neighbourhood of $r$ with $\Psi'(r)>0$. Then for every $x\in\mathbb R^n$,
--
--   $$
--   \|D^*(S\circ\Psi)(r,x)|^+=\Psi'(r)\,\|D^*S(\Psi(r),x)|^+ ,
--   $$
--
--   with the convention $\Psi'(r)\cdot(+\infty)=+\infty$.
--
--   In the proof of d) ⇒ a) of Theorem A the paper invokes the chain rule for coderivatives to obtain $\|D^*(S\circ\Psi)(r,x)|^+\le\|D^*S(\Psi(r),x)|^+/\bar\varphi(\Psi(r))\le1$ for the change of time with $\Psi'=1/\bar\varphi\circ\Psi$, $\bar\varphi=\max\{\varphi^\uparrow,1\}$. The identity above is the exact form of that step.
--
--   Differences from the source:
--   - encoding: moduli and talwegs with values in ℝ ∪ {+∞}, sup ∅ = 0 → values in ℝ≥0∞ (ENNReal.ofReal a = a⁺), empty supremum 0; reason: the values are nonnegative; [0, +∞] carries the usual topology of ℝ ∪ {+∞} restricted to it
--   - generalization: ‖D*(S ∘ Ψ)(r, x)|⁺ ≤ ‖D*S(Ψ(r), x)|⁺ / φ̄(Ψ(r)) ≤ 1 for all r ∈ (0, ρ), for the Ψ built in the proof of d) → a) → ‖D*(S ∘ Ψ)(r, x)|⁺ = Ψ′(r) · ‖D*S(Ψ(r), x)|⁺ for every S, every x and every Ψ that is C¹ near r with Ψ′(r) > 0; reason: with Ψ′ = 1/φ̄ ∘ Ψ this is the first inequality (as an equality), and the second is ‖D*S(Ψ(r), x)|⁺ ≤ φ↑(Ψ(r)) ≤ φ̄(Ψ(r)) by definition
-- source:
--   Daniilidis, Tapia-García, Desingularization of the Sweeping Process Mapping, arXiv:2110.08686v1, §4.2, proof of d) → a), display on p.15 (the chain rule [19, Theorem 10.37])

import Mathlib
import Definitions.Def_SweepingDesing_orientedModulus
open Filter Topology MeasureTheory Set
open scoped ENNReal

namespace SweepingDesing

/-- Daniilidis, Tapia-García, Desingularization of the Sweeping Process Mapping, arXiv:2110.08686v1, §4.2, proof of d) → a), display on p.15 (the chain rule for coderivatives
[Rockafellar–Wets, Theorem 10.37]): `‖D*(S ∘ Ψ)(r, x)|⁺ ≤ ‖D*S(Ψ(r), x)|⁺ / φ̄(Ψ(r)) ≤ 1`.
Stated here as the exact transformation rule behind it: if `Ψ` is `C¹` near `r` with
`Ψ'(r) > 0`, then for every `x`,
`‖D*(S ∘ Ψ)(r, x)|⁺ = Ψ'(r) · ‖D*S(Ψ(r), x)|⁺`.

**Formalization Note** Products in `[0, +∞]` (`Ψ'(r) · (+∞) = +∞`). With `Ψ' = 1/φ̄(Ψ)` it gives
the printed first inequality (as an equality), and the second is `‖D*S(Ψ(r), x)|⁺ ≤ φ↑(Ψ(r)) ≤ φ̄(Ψ(r))`.
No hypothesis on `S` is needed: the graph of `S ∘ Ψ` is, near `(r, x)`, the preimage of `gph S`
under the local `C¹` diffeomorphism `(r, x) ↦ (Ψ(r), x)`. -/
theorem orientedModulus_timeChange {n : ℕ} (S : ℝ → Set (EuclideanSpace ℝ (Fin n))) (Ψ : ℝ → ℝ) (r : ℝ)
    (hΨ : ∃ U ∈ 𝓝 r, ContDiffOn ℝ 1 Ψ U) (hΨ' : 0 < deriv Ψ r) (x : EuclideanSpace ℝ (Fin n)) :
    orientedModulus (fun r' => S (Ψ r')) r x = ENNReal.ofReal (deriv Ψ r) * orientedModulus S (Ψ r) x := by sorry

end SweepingDesing
