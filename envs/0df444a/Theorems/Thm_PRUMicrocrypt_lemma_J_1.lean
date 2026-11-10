-- Prove2me | Theorems.Thm_PRUMicrocrypt_lemma_J_1
-- name    : PRUMicrocrypt.lemma_J_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T22:28:09.426196+00:00
-- url     : https://prove2.me/theorems/fffcbbc8-13e4-4a5d-9597-5d257e965246
-- title:
--   Lemma J.1 — bounded polynomial certificates of mass $\pi^2d^2/4$
-- statement:
--   Let $m\ge0$ and $d\ge1$ be integers, and let $p:\{0,1\}^m\to[0,1]$ be a real polynomial of degree at most $d$. At every input $x$ there are nonnegative weights $c_i(x)$, $i\in[m]$, such that
--
--   $$|p(x)-p(x')|\le\sum_{i:\,x_i\ne x'_i}c_i(x)\quad\text{for every }x'\in\{0,1\}^m,\qquad \sum_{i=1}^m c_i(x)\le\frac{\pi^2d^2}{4}.$$
--
--   This is [ABD25, Theorem 1.7]. It gives the one-sided certificates of Lemma 6.2 and Corollary 6.7.
--
--   Differences from the source:
--   - encoding: a polynomial of degree at most d on {0,1}^m → agreement on {0,1}^m with a real MvPolynomial of total degree at most d; reason: the same functions
-- source:
--   Gulati–Khurana–Tomer, How to Build Pseudorandom Unitaries in Microcrypt, arXiv:2610.03711 (version of 2026-11-03, sha256 b591a3e5…), Lemma J.1, p.94

import Mathlib
import Definitions.Def_PRUMicrocrypt_sensitivity

set_option autoImplicit false

namespace PRUMicrocrypt

/-- **Lemma J.1 (Bounded polynomial certificates, [ABD25, Theorem 1.7]).** "Let m ≥ 0 and d ≥ 1 be
integers. Let p : {0, 1}^m → [0, 1] be a polynomial of degree at most d. At every input x, there are
nonnegative weights c_i(x), i ∈ [m], such that |p(x) − p(x′)| ≤ ∑_{i : x_i ≠ x′_i} c_i(x) for every
x′ ∈ {0, 1}^m, ∑_{i=1}^m c_i(x) ≤ π²d²/4. (J.1)"
A. Gulati, D. Khurana, K. Tomer, *How to Build Pseudorandom Unitaries in Microcrypt*,
arXiv:2610.03711 (version of 2026-11-03, sha256 b591a3e5…), Lemma J.1, p.94.

**Formalization Note.** "A polynomial of degree at most d" is a real multivariate polynomial of
total degree at most `d` evaluated at the Boolean point (`IsPolyDegLE`). -/
theorem lemma_J_1 (m d : ℕ) (hd : 1 ≤ d) (p : (Fin m → Bool) → ℝ) (hdeg : IsPolyDegLE d p)
    (hp : ∀ x, 0 ≤ p x ∧ p x ≤ 1) :
    ∀ x : Fin m → Bool, ∃ c : Fin m → ℝ, (∀ i, 0 ≤ c i) ∧
      (∀ x' : Fin m → Bool,
        |p x - p x'| ≤ ∑ i ∈ Finset.univ.filter (fun i => x i ≠ x' i), c i) ∧
      ∑ i, c i ≤ Real.pi ^ 2 * (d : ℝ) ^ 2 / 4 := by sorry

end PRUMicrocrypt
