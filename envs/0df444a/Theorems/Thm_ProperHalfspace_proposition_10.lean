-- Prove2me | Theorems.Thm_ProperHalfspace_proposition_10
-- name    : ProperHalfspace.proposition_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:03:44.382581+00:00
-- url     : https://prove2.me/theorems/f5a18b82-11ac-4eb5-a72e-54675793495e
-- title:
--   Proposition 10 — search over affine halfspaces and uniform convergence (corrected: $(m+1)^{C(D+1)}$ time and $D+1+\log(1/\beta)$ samples)
-- statement:
--   Let $\Phi:\{\pm1\}^n\to\mathbb R^D$ be any map, and for labels in $[-1,1]$ write $\widehat{\mathrm{err}}_S(h\circ\Phi)=\frac1m\sum_j(1-y_jh(\Phi(x_j)))/2$ and $\mathrm{err}_P(h\circ\Phi)=\mathbf E_{(x,y)\sim P}[(1-yh(\Phi(x)))/2]$. On labels $\pm1$ these are the indicator errors.
--
--   1. There is one program and a universal $C$ such that, given $m\ge1$, $D$, mapped points $\varphi_1,\dots,\varphi_m\in\mathbb R^D$ and labels $y_j\in[-1,1]$, the program halts within $(m+1)^{C(D+1)}$ steps with an affine halfspace minimizing the empirical error over all affine halfspaces on $\mathbb R^D$.
--   2. There is a universal $C$ such that for every probability distribution $P$ on $\{\pm1\}^n\times[-1,1]$, every $\varepsilon>0$, every $\beta\in(0,1)$ and every
--   $$m\ge C\,\frac{D+1+\log(1/\beta)}{\varepsilon^2},$$
--   with probability at least $1-\beta$ over $S\sim P^m$, every affine halfspace $h$ on $\mathbb R^D$ satisfies $|\widehat{\mathrm{err}}_S(h\circ\Phi)-\mathrm{err}_P(h\circ\Phi)|\le\varepsilon$.
--   3. On this event, every empirical minimizer $h_S$ satisfies $\mathrm{err}_P(h_S\circ\Phi)\le\min_h\mathrm{err}_P(h\circ\Phi)+2\varepsilon$.
--
--   This is the empirical risk minimization step of the learner.
--
--   Differences from the source:
--   - correction: time m^{O(D)} → (m+1)^{C(D+1)}, with m ≥ 1; reason: false as printed at D = 0, where m^{O(D)} = 1 though the minimizer is the sign of a sum of m labels, and at m = 1, where it is 1 though the output has D + 1 numbers; equal to m^{O(D)} for m ≥ 2, D ≥ 1
--   - correction: m ≥ C(D + log(1/β))/ε² → m ≥ C(D + 1 + log(1/β))/ε²; reason: false as printed: D = 0, y a uniform sign, ε = 1/4, m = 1, β = exp(−1/(16C)) meets it, while err_S ∈ {0,1} and err_P = 1/2; the corrected form implies the printed one for D ≥ 1 and for D = 0 with β ≤ 1/2, and Algorithm 1 itself uses D + 1
--   - generalization: the Boolean clause and the [−1,1] clause, stated separately → one statement for labels in [−1,1]; reason: (1 − y h)/2 is the indicator on y = ±1, so the Boolean clause is the special case
--   - reading: the real-RAM model, with no instruction set named (p.2) → the local machine ProperHalfspace.Machine, with exact + − × ÷, rational literals, fair coins, query at cost n, and no √, floor, eigensolver or uniform real draw; reason: the page names no instructions; every primitive added would weaken the theorem
--   - encoding: min_h in the conclusion, and h_S the algorithm's output → for every h, and for every empirical minimizer h_S; reason: no attainment is needed, and the algorithm's output is one such minimizer
--   - encoding: ε and β with no stated range → 0 < ε and 0 < β < 1; reason: the conditions under which ε⁻² and log(1/β) are defined; at β ≥ 1 the probability claim is empty and the clause on the event is deterministic, so no instance of the page is lost
--   - encoding: a distribution on {±1}ⁿ × {±1} (or × [−1,1]) → a probability measure on Cube n × ℝ whose label is in [−1,1] almost surely; reason: the same distributions
-- source:
--   De, Mossel, Nadimpalli, Neeman, Efficient Proper Agnostic Learning of Halfspaces, arXiv:2611.02344 (Nov. 1, 2026), Proposition 10, pp.16–17

import Mathlib
import Definitions.Def_ProperHalfspace_Machine
import Definitions.Def_ProperHalfspace_AffineERM

open MeasureTheory

namespace ProperHalfspace

/-- Proposition 10, pp.16–17 (efficient search over affine halfspaces), with `(m+1)^{C(D+1)}` and `D + 1 + log(1/β)` (corrected at
`D = 0` and `m = 1`). De, Mossel, Nadimpalli, Neeman, arXiv:2611.02344 (Nov. 1, 2026). All three parts for labels in `[−1, 1]`, which
contain the page's Boolean clause.
(a) One program finds a minimizer of the weighted empirical error over all affine halfspaces on `ℝᴰ`, in `(m+1)^{C(D+1)}` steps.
(b) With `P^m`-probability at least `1 − β`, every affine halfspace has `|err_S − err_P| ≤ ε`, once
`m ≥ C (D + 1 + log(1/β))/ε²`.
(c) On that event, every empirical minimizer `h_S` has `err_P(h_S ∘ Φ) ≤ err_P(h ∘ Φ) + 2ε` for every `h`.

**Formalization Note.** On labels `y = ±1`, `(1 − y h)/2` is the indicator `1{h ≠ y}`. In (a) the program uses no coin and no query
(`NoOracle`), so the oracle and tape arguments of `run` are immaterial. In (c), "min" is written as "for every `h`". -/
theorem proposition_10 :
    (∃ P : Program, Admissible P ∧ NoOracle P ∧ ∃ C : ℕ, ∀ (m D : ℕ), 1 ≤ m →
      ∀ (φ : Fin m → Fin D → ℝ) (y : Fin m → ℝ), (∀ j, |y j| ≤ 1) →
        ∃ t : ℕ,
          let s := run P (fun _ : Cube 0 => (0 : ℝ)) (fun _ => false) (ermInit φ y) t
          s.halted = true ∧ s.work ≤ (m + 1) ^ (C * (D + 1)) ∧
          ∀ (w : Fin D → ℝ) (θ : ℝ),
            empErr φ y (decodeNormal D s) (decodeThreshold D s) ≤ empErr φ y w θ) ∧
    (∃ C : ℝ, ∀ (n D : ℕ) (Φ : Cube n → Fin D → ℝ) (P : Measure (Cube n × ℝ)) [IsProbabilityMeasure P],
      (∀ᵐ p ∂P, |p.2| ≤ 1) → ∀ ε β : ℝ, 0 < ε → 0 < β → β < 1 → ∀ m : ℕ,
        C * ((D : ℝ) + 1 + Real.log (1 / β)) / ε ^ 2 ≤ (m : ℝ) →
        let Good : (Fin m → Cube n × ℝ) → Prop := fun S => ∀ (w : Fin D → ℝ) (θ : ℝ),
          |empErr (fun j => Φ (S j).1) (fun j => (S j).2) w θ - popErr P Φ w θ| ≤ ε
        1 - β ≤ (Measure.pi fun _ : Fin m => P).real {S | Good S} ∧
        ∀ S, Good S → ∀ (wS : Fin D → ℝ) (θS : ℝ),
          (∀ (w : Fin D → ℝ) (θ : ℝ),
            empErr (fun j => Φ (S j).1) (fun j => (S j).2) wS θS ≤
              empErr (fun j => Φ (S j).1) (fun j => (S j).2) w θ) →
          ∀ (w : Fin D → ℝ) (θ : ℝ), popErr P Φ wS θS ≤ popErr P Φ w θ + 2 * ε) := by sorry

end ProperHalfspace
