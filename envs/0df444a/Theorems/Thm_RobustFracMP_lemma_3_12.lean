-- Prove2me | Theorems.Thm_RobustFracMP_lemma_3_12
-- name    : RobustFracMP.lemma_3_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T18:00:12.602637+00:00
-- url     : https://prove2.me/theorems/66876e5b-ed21-48e8-a218-bd2741405e90
-- title:
--   Lemma 3.12 — $\mathrm{MP}_\beta$ without distortion is an LMP $2^{O(z^2)}\beta^{-1}$-approximation
-- statement:
--   Let $\beta^*=2^{-z-1}$. There is an absolute constant $C$ such that for every integer $z\ge1$, every finite nonempty metric space $(P,\mathrm{dist})$, every opening cost $\lambda>0$ and every scale factor $\beta\in(0,\beta^*]$, the output $y^{(\beta)}$ of Algorithm 1 run on $(P,\mathrm{dist})$ is a fractional solution of Power-$z$ Facility Location ($y^{(\beta)}\ge0$ and $\|y^{(\beta)}\|_1\ge1$) and
--
--   $$\mathrm{cost}_z(y^{(\beta)})\le2^{Cz^2}\,\beta^{-1}\bigl(\widehat{\mathrm{OPT}}^{\mathrm{fl}}_z(\lambda)-\lambda\|y^{(\beta)}\|_1\bigr).$$
--
--   This is the undistorted case of the goal; in the proof of Lemma 3.1 it is applied at $\beta=\beta^*$, giving (17).
--
--   Differences from the source:
--   - reading: 2^{O(z²)} → 2^{C·z²} for one real constant C, quantified before P, z and all other data; reason: O(z²) hides an absolute constant; the paper's constants (γ* = 2^{2z²+z}, 2^{O(z)}) do not depend on P, λ, β or ε
--   - encoding: 'returns a fractional solution y^{(β)}' → (∀ p, 0 ≤ y p) ∧ 1 ≤ ∑ p, y p; reason: Power-z Facility Location's fractional solutions are y ∈ ℝ^P_{≥0} with ‖y‖₁ ≥ 1 (p.11)
--   - encoding: ‖y‖₁ for y ≥ 0 → ∑ p, y p; reason: the entries are nonnegative, so the sum is the ℓ₁ norm
--   - encoding: a dataset P in a metric space (finite; a fractional solution with ‖y‖₁ ≥ 1 exists) → P a type with Fintype, Nonempty and MetricSpace instances; reason: the dataset is a finite set of points; nonemptiness only excludes the empty dataset, which has no fractional solution
-- source:
--   Czumaj–Jiang–Jin–Lou–Wang, Fully Scalable MPC Algorithms for Euclidean Clustering, arXiv:2604.00954 (version of November 3, 2026; manuscript sha256 c65896fe…51d8), Lemma 3.12, p.19 (PDF p.21)

import Mathlib
import Definitions.Def_RobustFracMP_fracCost
import Definitions.Def_RobustFracMP_optFL
import Definitions.Def_RobustFracMP_mpOutput

set_option autoImplicit false

namespace RobustFracMP

universe u

/-- **Lemma 3.12 (MP_β without distance distortions is an LMP 2^{O(z²)}β^{−1}-approximation).**

Czumaj–Jiang–Jin–Lou–Wang, *Fully Scalable MPC Algorithms for Euclidean Clustering*,
arXiv:2604.00954 (version of November 3, 2026; manuscript sha256 c65896fe…51d8), Lemma 3.12, p.19 (PDF p.21): "Let β* := 2^{−z−1} and let (P, dist) be a metric space. For any
scale factor β ∈ (0, β*], the algorithm MP_β (Algorithm 1) on input (P, dist) returns a fractional
solution y^{(β)} to Power-z Facility Location with an LMP 2^{O(z²)}β^{−1}-approximation guarantee,
i.e., cost_z(y^{(β)}) ≤ 2^{O(z²)} · β^{−1} · (\widehat{OPT}^{fl}_z(λ) − λ · ‖y^{(β)}‖₁)."

All clauses are stated: `y^{(β)} ≥ 0` and `‖y^{(β)}‖₁ ≥ 1` (a fractional solution), and the LMP
inequality. `2^{O(z²)}` is `2^{C·z²}` with one absolute constant `C` quantified first.

**Formalization Note.** `‖y‖₁` is `∑ p, y p`. `(P, dist)` is a finite nonempty metric space (the
dataset). Standing hypotheses of Sections 2–3 (pp.10–14): `z ≥ 1` an integer, `(P, dist)` a finite
metric space (the dataset, with `F = P`), opening cost `λ > 0`; `r^{(β)}_p` is
`mpRadius z dist β lam p`, computed on the true metric (p.14). -/
theorem lemma_3_12 : ∃ C : ℝ, ∀ (P : Type u) [Fintype P] [Nonempty P] [MetricSpace P] (z : ℕ),
    1 ≤ z → ∀ lam : ℝ, 0 < lam → ∀ β : ℝ, 0 < β → β ≤ 1 / 2 ^ (z + 1) →
      (∀ p, 0 ≤ mpOutput (P := P) z dist β lam p) ∧ 1 ≤ ∑ p, mpOutput (P := P) z dist β lam p ∧
      fracCost z (mpOutput (P := P) z dist β lam) ≤
        (2 : ℝ) ^ (C * (z : ℝ) ^ 2) * β⁻¹ *
          (optFL P z lam - lam * ∑ p, mpOutput (P := P) z dist β lam p) := by sorry

end RobustFracMP
