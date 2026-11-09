-- Prove2me | Theorems.Thm_UnaryParityLifting_Exact_averaging_properties
-- name    : UnaryParityLifting.Exact.averaging_properties
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:09:43.162824+00:00
-- url     : https://prove2.me/theorems/4faa384b-966d-41e9-9631-4771a3fd1949
-- title:
--   Proposition 3.3 — Properties of gadget averaging
-- statement:
--   Let $g:\{0,1\}^m\to\{0,1\}$ be surjective, and let $A_g$ average a real function of $N$ blocks uniformly over the fiber of the prescribed output. The operator is additive and homogeneous over $\mathbb R$, maps nonnegative functions to nonnegative functions, and preserves every constant. For every real block function $f$ and every real outer function $\varphi$,
--   $$\|A_gf\|_\infty\le\|f\|_\infty,\qquad A_g(\varphi\circ g^N)=\varphi.$$
--
--   The sup norm is a finite maximum on the cube. This statement includes all the source's algebraic, order and norm properties in one item. No balance or stifling assumption is added to this proposition.
--
--   Differences from the source:
--   - encoding: coordinates indexed by [N] and [m], bits in {0,1} → Fin N and Fin m, Bool bits with false = 0 and true = 1; reason: zero-based labels and the explicit bit maps preserve every assignment
-- source:
--   Yaroslav Alekseev, Lifting to Unary Sherali–Adams over Parities, STOC 2027 submission #567 (October 2026), citation_basis: published; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/567.pdf; p.9, Proposition 3.3

import Mathlib
import Definitions.Def_UnaryParityLifting_Exact_averaging

namespace UnaryParityLifting.Exact

/-- Alekseev, STOC 2027 submission #567 (October 2026), p.9, Proposition 3.3. -/
theorem averaging_properties (m N : ℕ) (g : (Fin m → Bool) → Bool)
    (hg : Function.Surjective g) :
    (∀ f h : (Fin N × Fin m → Bool) → ℝ,
      average g (fun X => f X + h X) = fun z => average g f z + average g h z) ∧
    (∀ (a : ℝ) (f : (Fin N × Fin m → Bool) → ℝ),
      average g (fun X => a * f X) = fun z => a * average g f z) ∧
    (∀ f : (Fin N × Fin m → Bool) → ℝ,
      (∀ X, 0 ≤ f X) → ∀ z, 0 ≤ average g f z) ∧
    (∀ a : ℝ, average g (fun _ : Fin N × Fin m → Bool => a) = fun _ => a) ∧
    (∀ f : (Fin N × Fin m → Bool) → ℝ, cubeSup (average g f) ≤ cubeSup f) ∧
    (∀ φ : (Fin N → Bool) → ℝ,
      average g (fun X => φ (blockMap g X)) = φ) := by sorry

end UnaryParityLifting.Exact
