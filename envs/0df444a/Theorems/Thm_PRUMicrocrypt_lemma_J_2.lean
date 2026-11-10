-- Prove2me | Theorems.Thm_PRUMicrocrypt_lemma_J_2
-- name    : PRUMicrocrypt.lemma_J_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T22:28:07.008885+00:00
-- url     : https://prove2.me/theorems/85956c32-8adc-4ba0-b3a4-26e15fce0a0b
-- title:
--   Lemma J.2 — a sensitivity bound from one-sided certificates
-- statement:
--   Let $m\ge0$ and $C\ge1$, and suppose every input of $f:\{0,1\}^m\to[0,1]$ has a one-sided certificate of mass at most $C$. For a uniform $X\in\{0,1\}^m$, every $0<\delta\le1$ and every $t\ge0$,
--
--   $$\Pr[S_\delta(f,X)\ge t]\le\frac2\delta\,2^{-t\delta/(16C)}.$$
--
--   Combined with Lemma J.1 this proves Lemma 6.2.
--
--   Differences from the source:
--   - reading: every t ≥ 0 → every real t ≥ 0; reason: S_δ is integer valued; a real threshold contains every integer one
-- source:
--   Gulati–Khurana–Tomer, How to Build Pseudorandom Unitaries in Microcrypt, arXiv:2610.03711 (version of 2026-11-03, sha256 b591a3e5…), Lemma J.2, p.94

import Mathlib
import Definitions.Def_PRUMicrocrypt_sensitivity

set_option autoImplicit false

namespace PRUMicrocrypt

/-- **Lemma J.2 (A sensitivity bound from one-sided certificates).** "Let m ≥ 0 and C ≥ 1. Suppose
every input of f : {0, 1}^m → [0, 1] has a one-sided certificate of mass at most C. For uniform
X ∈ {0, 1}^m, every 0 < δ ≤ 1, and every t ≥ 0, Pr[S_δ(f, X) ≥ t] ≤ (2/δ) 2^{−tδ/(16C)}. (J.2)"
A. Gulati, D. Khurana, K. Tomer, *How to Build Pseudorandom Unitaries in Microcrypt*,
arXiv:2610.03711 (version of 2026-11-03, sha256 b591a3e5…), Lemma J.2, p.94 (one-sided certificates and `S_δ` defined just before it, p.94).

**Formalization Note.** `t` is a real number; `Pr` is the uniform probability on `{0,1}ᵐ`. -/
theorem lemma_J_2 (m : ℕ) (C : ℝ) (hC : 1 ≤ C) (f : (Fin m → Bool) → ℝ)
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1)
    (hcert : ∀ y, ∃ w : Fin m → ℝ, IsOneSidedCert f y w ∧ ∑ i, w i ≤ C) :
    ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ t : ℝ, 0 ≤ t →
      unifProb (fun X : Fin m → Bool => t ≤ (sensitivity δ f X : ℝ)) ≤
        (2 / δ) * (2 : ℝ) ^ (-(t * δ) / (16 * C)) := by sorry

end PRUMicrocrypt
