-- Prove2me | Theorems.Thm_PRUMicrocrypt_lemma_6_3
-- name    : PRUMicrocrypt.lemma_6_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T22:28:17.865653+00:00
-- url     : https://prove2.me/theorems/02ecb05d-a05d-440c-b5c3-0134453fd200
-- title:
--   Lemma 6.3 — from sensitivity to average change
-- statement:
--   Let $m\ge1$, $f:\{0,1\}^m\to[0,1]$ and $0<\delta\le1$. For every input $x$,
--
--   $$A_f(x)\le\delta+\frac{S_\delta(f,x)}{m}.$$
--
--   Consequently, for a uniform input $X$ and every $t\ge0$,
--
--   $$\Pr_X[A_f(X)>\delta+t/m]\le\Pr_X[S_\delta(f,X)\ge t].$$
--
--   The lemma converts the sensitivity tail of Lemma 6.5 into a bound on the average change of a score under a random switch flip.
--
--   Differences from the source:
--   - reading: every t ≥ 0 → every real t ≥ 0; reason: a real threshold contains every integer one
-- source:
--   Gulati–Khurana–Tomer, How to Build Pseudorandom Unitaries in Microcrypt, arXiv:2610.03711 (version of 2026-11-03, sha256 b591a3e5…), Lemma 6.3, p.34

import Mathlib
import Definitions.Def_PRUMicrocrypt_sensitivity

set_option autoImplicit false

namespace PRUMicrocrypt

/-- **Lemma 6.3 (From sensitivity to average change).** "Let m ≥ 1, let f : {0, 1}^m → [0, 1], and
let 0 < δ ≤ 1. For every input x, A_f(x) ≤ δ + S_δ(f, x)/m. Consequently, for a uniform input X and
every t ≥ 0, Pr_X[A_f(X) > δ + t/m] ≤ Pr_X[S_δ(f, X) ≥ t]. (6.2)"
A. Gulati, D. Khurana, K. Tomer, *How to Build Pseudorandom Unitaries in Microcrypt*,
arXiv:2610.03711 (version of 2026-11-03, sha256 b591a3e5…), Lemma 6.3, p.34.

**Formalization Note.** Both clauses are stated; `t` is a real number. -/
theorem lemma_6_3 (m : ℕ) (hm : 1 ≤ m) (f : (Fin m → Bool) → ℝ) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    (∀ x, avgChange f x ≤ δ + (sensitivity δ f x : ℝ) / m) ∧
    ∀ t : ℝ, 0 ≤ t →
      unifProb (fun X : Fin m → Bool => δ + t / m < avgChange f X) ≤
        unifProb (fun X : Fin m → Bool => t ≤ (sensitivity δ f X : ℝ)) := by sorry

end PRUMicrocrypt
