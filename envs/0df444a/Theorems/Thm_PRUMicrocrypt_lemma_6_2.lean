-- Prove2me | Theorems.Thm_PRUMicrocrypt_lemma_6_2
-- name    : PRUMicrocrypt.lemma_6_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T22:28:07.035463+00:00
-- url     : https://prove2.me/theorems/412924ed-e351-4204-8f4c-5d5d06bd71c9
-- title:
--   Lemma 6.2 — sensitivity of a maximum of polynomials
-- statement:
--   Let $m\ge0$ and $D\ge1$ be integers, and let $(p_a)_{a\in I}$ be a family of real polynomials on $\{0,1\}^m$, each of degree at most $D$ and with values in $[0,1]$. Let $f(x)=\max_{a\in I}p_a(x)$ for every $x$. For every $0<\delta\le1$ and $t\ge0$,
--
--   $$\Pr_{X\sim\{0,1\}^m}[S_\delta(f,X)\ge t]\le\frac2\delta\,2^{-t\delta/(4\pi^2D^2)}.$$
--
--   In Section 6 this is applied to the optimal acceptance probability $g_z$, which is a maximum over witnesses of low-degree acceptance polynomials in the free row switches.
--
--   Differences from the source:
--   - reading: f(x) = max_{a∈I} p_a(x) for every x → f(x) is the greatest element of {p_a(x) : a ∈ I} for every x (attained maximum); reason: a maximum presupposes attainment, and the proof (J.3) picks a maximizer
--   - reading: every t ≥ 0 → every real t ≥ 0; reason: a real threshold contains every integer one
--   - encoding: real-valued polynomials of degree at most D on {0,1}^m → agreement on {0,1}^m with a real MvPolynomial of total degree at most D; reason: the same functions
-- source:
--   Gulati–Khurana–Tomer, How to Build Pseudorandom Unitaries in Microcrypt, arXiv:2610.03711 (version of 2026-11-03, sha256 b591a3e5…), Lemma 6.2, pp.33–34 (proof §J.3, p.96)

import Mathlib
import Definitions.Def_PRUMicrocrypt_sensitivity

set_option autoImplicit false

namespace PRUMicrocrypt

/-- **Lemma 6.2 (Sensitivity of a maximum of polynomials).** "Let m ≥ 0 and D ≥ 1 be integers. Let
(p_a)_{a∈I} be a family of real-valued polynomials on {0, 1}^m, each of degree at most D and with
values in [0, 1]. Define the pointwise maximum f(x) = max_{a∈I} p_a(x) for every x. For every
0 < δ ≤ 1 and t ≥ 0, Pr_{X∼{0,1}^m}[S_δ(f, X) ≥ t] ≤ (2/δ) 2^{−tδ/(4π²D²)}."
A. Gulati, D. Khurana, K. Tomer, *How to Build Pseudorandom Unitaries in Microcrypt*,
arXiv:2610.03711 (version of 2026-11-03, sha256 b591a3e5…), Lemma 6.2, pp.33–34.

**Formalization Note.** The index family `I` is arbitrary; "`f(x) = max_a p_a(x)` for every `x`" is
read as an attained maximum (`IsGreatest`), as the proof (J.3, p.96) picks a maximizer. `t` is a
real number. -/
theorem lemma_6_2 (m D : ℕ) (hD : 1 ≤ D) {I : Type*} (p : I → (Fin m → Bool) → ℝ)
    (hdeg : ∀ a, IsPolyDegLE D (p a)) (hp : ∀ a x, 0 ≤ p a x ∧ p a x ≤ 1)
    (f : (Fin m → Bool) → ℝ) (hf : ∀ x, IsGreatest (Set.range fun a => p a x) (f x)) :
    ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ t : ℝ, 0 ≤ t →
      unifProb (fun X : Fin m → Bool => t ≤ (sensitivity δ f X : ℝ)) ≤
        (2 / δ) * (2 : ℝ) ^ (-(t * δ) / (4 * Real.pi ^ 2 * (D : ℝ) ^ 2)) := by sorry

end PRUMicrocrypt
