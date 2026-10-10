-- Prove2me | Theorems.Thm_ProxADMMLC_Conv_lemma_3_2
-- name    : ProxADMMLC.Conv.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:47:39.028024+00:00
-- url     : https://prove2.me/theorems/ab3efd05-b12c-4946-a3d0-6c8fed653940
-- title:
--   Lemma 3.2 (dual ascent), p. 2278 — lower bound on d(yᵗ⁺¹, zᵗ⁺¹) − d(yᵗ, zᵗ)
-- statement:
--   Let $x(y,z)$ be a minimizer of $K(\cdot,z;y)$ over $P$ and $d(y,z)$ its value (2.6)–(2.7). For every run $(x^t,y^t,z^t)$ of Algorithm 2.2 (with any parameters) and every $t$,
--   $$d(y^{t+1},z^{t+1})-d(y^t,z^t)\ \ge\ \alpha(Ax^t-b)^\top\big(Ax(y^{t+1},z^t)-b\big)+\frac p2\,(z^{t+1}-z^t)^\top\big(z^{t+1}+z^t-2x(y^{t+1},z^{t+1})\big).$$
--
--   The dual function $d$ can only lose by the amounts on the right; together with Lemmas 3.1 and 3.3 this controls the change of the potential $\phi^t$.
--
--   **Formalization Note** No assumption on $f$ or on the parameters is needed: the proof only compares values of $K$ at minimizers.
-- source:
--   Zhang & Luo, A proximal alternating direction method of multiplier for linearly constrained nonconvex minimization, SIAM J. Optim. 30(3) (2020), p. 2278, Lemma 3.2

import Mathlib
import Definitions.Def_ProxADMMLC_Conv_Setting

namespace ProxADMMLC.Conv

theorem lemma_3_2 {n m : ℕ} (f : E n → ℝ) (A : E n →L[ℝ] E m) (b : E m) (ℓ u : Fin n → ℝ)
    (Γ p c α β : ℝ) (xs : E m → E n → E n) (hxs : IsXSel f A b ℓ u Γ p xs)
    (x z : ℕ → E n) (y : ℕ → E m) (hrun : IsRun f A b ℓ u Γ p c α β x y z) :
    ∀ t, dval f A b Γ p xs (y (t + 1)) (z (t + 1)) - dval f A b Γ p xs (y t) (z t) ≥
      α * inner ℝ (A (x t) - b) (A (xs (y (t + 1)) (z t)) - b) +
        p / 2 * inner ℝ (z (t + 1) - z t)
          (z (t + 1) + z t - (2 : ℝ) • xs (y (t + 1)) (z (t + 1))) := by sorry

end ProxADMMLC.Conv
