-- Prove2me | Theorems.Thm_RobustFracMP_lemma_3_16
-- name    : RobustFracMP.lemma_3_16
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:59:00.176568+00:00
-- url     : https://prove2.me/theorems/a660915e-8011-4337-8e88-1ffc21abe877
-- title:
--   Lemma 3.16 — $\mathrm{cost}_z(y^{(\beta)})\le2^{O(z^2)}\sigma_z(x^{(\beta)})$
-- statement:
--   Throughout, $z\ge 1$ is an integer, $(P,\mathrm{dist})$ is a finite nonempty metric space (the dataset, with candidate centers $F=P$), $\lambda>0$ is the opening cost, and $r^{(\beta)}_p$ is the radius of Algorithm 1 computed on the true metric $\mathrm{dist}$; $[a]_+=\max\{a,0\}$.
--
--   There is an absolute constant $C$ such that for every integer $z\ge1$, every finite nonempty metric space $(P,\mathrm{dist})$, every $\lambda>0$ and every $\beta\in(0,2^{-z-1}]$, the output $y^{(\beta)}$ of Algorithm 1 on $(P,\mathrm{dist})$ satisfies $\|y^{(\beta)}\|_1\ge1$ and
--
--   $$\mathrm{cost}_z(y^{(\beta)})\le2^{Cz^2}\,\sigma_z(x^{(\beta)}).$$
--
--   Since $x^{(\beta)}$ need not be feasible for $y^{(\beta)}$ when $z\ge2$ (Example 3.19), this lemma is needed to pass from the assignment cost of Lemma 3.14 to the clustering cost; together they give Lemma 3.12.
--
--   Differences from the source:
--   - reading: stated inside the proof of Lemma 3.12, whose statement fixes β ∈ (0, β*], β* = 2^{−z−1} (p.19) → hypotheses 0 < β and β ≤ 1 / 2 ^ (z + 1); reason: the claim's own sentence names no range for β; its context does
--   - reading: 2^{O(z²)} → 2^{C·z²} for one real constant C, quantified before P, z and all other data; reason: O(z²) hides an absolute constant; the paper's constants (γ* = 2^{2z²+z}, 2^{O(z)}) do not depend on P, λ, β or ε
--   - generalization: cost_z(y^{(β)}) ≤ 2^{O(z²)} σ_z(x^{(β)}) → additionally asserts Σ_p y^{(β)}_p ≥ 1; reason: the paper proves it (Lemma 3.12: MP_β returns a fractional solution; it follows from Lemma 3.9); the clause guarantees cost_z(y^{(β)}) is defined, and the Lean statement implies the printed one
--   - encoding: ‖y‖₁ for y ≥ 0 → ∑ p, y p; reason: the entries are nonnegative, so the sum is the ℓ₁ norm
--   - encoding: a dataset P in a metric space (finite; a fractional solution with ‖y‖₁ ≥ 1 exists) → P a type with Fintype, Nonempty and MetricSpace instances; reason: the dataset is a finite set of points; nonemptiness only excludes the empty dataset, which has no fractional solution
-- source:
--   Czumaj–Jiang–Jin–Lou–Wang, Fully Scalable MPC Algorithms for Euclidean Clustering, arXiv:2604.00954 (version of November 3, 2026; manuscript sha256 c65896fe…51d8), Lemma 3.16, p.22 (PDF p.24)

import Mathlib
import Definitions.Def_RobustFracMP_assignCost
import Definitions.Def_RobustFracMP_fracCost
import Definitions.Def_RobustFracMP_mpOutput
import Definitions.Def_RobustFracMP_xBeta

set_option autoImplicit false

namespace RobustFracMP

universe u

/-- **Lemma 3.16 (cost of y^{(β)} against the assignment cost of x^{(β)}).**

Czumaj–Jiang–Jin–Lou–Wang, *Fully Scalable MPC Algorithms for Euclidean Clustering*,
arXiv:2604.00954 (version of November 3, 2026; manuscript sha256 c65896fe…51d8), Lemma 3.16, p.22 (PDF p.24): "cost_z(y^{(β)}) ≤ 2^{O(z²)} · σ_z(x^{(β)})."

The lemma sits inside the proof of Lemma 3.12, which fixes `β ∈ (0, β*]`, `β* = 2^{−z−1}` (p.19).
`2^{O(z²)}` is read as `2^{C·z²}` for one absolute constant `C`, quantified before the space, `z`,
`λ` and `β`. The statement also asserts `‖y^{(β)}‖₁ ≥ 1`, which the paper establishes (Lemma 3.12
says MP_β "returns a fractional solution"; it follows from Lemma 3.9), so that `cost_z(y^{(β)})`
is the paper's value and not the empty-infimum junk.

**Formalization Note.** `2 ^ (C * z ^ 2)` is the real power. Standing hypotheses of Sections 2–3 (pp.10–14): `z ≥ 1` an integer, `(P, dist)` a finite
metric space (the dataset, with `F = P`), opening cost `λ > 0`; `r^{(β)}_p` is
`mpRadius z dist β lam p`, computed on the true metric (p.14). -/
theorem lemma_3_16 : ∃ C : ℝ, ∀ (P : Type u) [Fintype P] [Nonempty P] [MetricSpace P] (z : ℕ),
    1 ≤ z → ∀ lam : ℝ, 0 < lam → ∀ β : ℝ, 0 < β → β ≤ 1 / 2 ^ (z + 1) →
      1 ≤ ∑ p, mpOutput (P := P) z dist β lam p ∧
      fracCost z (mpOutput (P := P) z dist β lam) ≤
        (2 : ℝ) ^ (C * (z : ℝ) ^ 2) * assignCost z (xBeta (P := P) z β lam) := by sorry

end RobustFracMP
