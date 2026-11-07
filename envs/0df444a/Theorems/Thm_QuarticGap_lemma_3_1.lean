-- Prove2me | Theorems.Thm_QuarticGap_lemma_3_1
-- name    : QuarticGap.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:45:18.270209+00:00
-- url     : https://prove2.me/theorems/7bd12616-cb34-4ef6-b05f-c4bc0b4030e7
-- title:
--   Lemma 3.1 — moments of $Z_s$, and the bounds and limits of $c_M$, $a_M$, $b_M$
-- statement:
--   Let $m \ge 2$, $M = 2^m$, let $f$ be uniformly random and $s \in \{0,1\}^m$. Then $Z_s = Z_s(f)$ has the distribution of $M^{-1/2}$ times a sum of $M$ independent uniform signs, so $\mathbb E Z_s^2 = 1$ and $\mathbb E Z_s^4 = 3-2/M$. Moreover $\mathbb E \sin Z_s = \mathbb E[Z_s\cos Z_s] = \mathbb E[Z_s^2\sin Z_s] = 0$, and
--   $$
--   \mathbb E\cos Z_s = c_M, \qquad \mathbb E[Z_s^2\cos Z_s] = a_M, \qquad \mathbb E[Z_s\sin Z_s] = b_M .
--   $$
--   For $M \ge 4$,
--   $$
--   \tfrac12 \le c_M \le e^{-1/2}, \quad 0 \le a_M \le \frac{1}{3M}, \quad \Bigl(1-\frac{1}{6M}\Bigr)e^{-1/2} \le b_M \le 1, \quad a_M-c_M \le -\frac{5}{12} .
--   $$
--   As $M \to \infty$, $c_M \to e^{-1/2}$, $a_M \to 0$ and $b_M \to e^{-1/2}$.
--
--   These moments determine the bias of both test functions.
--
--   **Formalization Note** Equality of distributions is written as equality of the probability of each value.
--
--   Differences from the source:
--   - encoding: independent uniform signs, uniformly random f or W → the uniform distribution on the finite set of sign functions; reason: the same law
--   - encoding: M → ∞ → m → ∞ along M = 2^m; reason: M is a power of two throughout the section
-- source:
--   Chakrabarti, Herman, Kim, Ozgul, The Quartic Gap Between Quantum and Dequantized Algorithms for Linear Algebra Is Tight, arXiv:2610.42069 (file sha256 9f68aaf9…), Lemma 3.1, p.23

import Mathlib
import Definitions.Def_QuarticGap_Phi

open QAlgorithms

namespace QuarticGap

/-- Lemma 3.1 (arXiv:2610.42069 (file sha256 9f68aaf9…), p.23). For uniformly random `f` and every
`s`: `Z_s` has the distribution of `M^{−1/2}` times a sum of `M` independent uniform signs; the
moments `𝔼Z_s² = 1`, `𝔼Z_s⁴ = 3 − 2/M`; `𝔼 sin Z_s = 𝔼[Z_s cos Z_s] = 𝔼[Z_s² sin Z_s] = 0`;
`𝔼 cos Z_s = c_M`, `𝔼[Z_s² cos Z_s] = a_M`, `𝔼[Z_s sin Z_s] = b_M`; the bounds (9) for `M ≥ 4`; and the
limits as `M → ∞`.

**Formalization Note** The section fixes `m ≥ 2`, which is `M ≥ 4`. The `M` independent uniform signs
are a uniform `g : {0,1}^m → {−1,1}`; equality of distributions is equality of the probability of
every value. -/
theorem lemma_3_1 :
    (∀ {m : ℕ}, 2 ≤ m → ∀ s : Qubits m,
      (∀ t : ℝ, uProb (fun f : Qubits m → ℤˣ => Zs f s = t) =
        uProb (fun g : Qubits m → ℤˣ => (Real.sqrt (bigM m))⁻¹ * ∑ σ, sgn (g σ) = t)) ∧
      uAvg (fun f : Qubits m → ℤˣ => Zs f s ^ 2) = 1 ∧
      uAvg (fun f : Qubits m → ℤˣ => Zs f s ^ 4) = 3 - 2 / bigM m ∧
      uAvg (fun f : Qubits m → ℤˣ => Real.sin (Zs f s)) = 0 ∧
      uAvg (fun f : Qubits m → ℤˣ => Zs f s * Real.cos (Zs f s)) = 0 ∧
      uAvg (fun f : Qubits m → ℤˣ => Zs f s ^ 2 * Real.sin (Zs f s)) = 0 ∧
      uAvg (fun f : Qubits m → ℤˣ => Real.cos (Zs f s)) = cM m ∧
      uAvg (fun f : Qubits m → ℤˣ => Zs f s ^ 2 * Real.cos (Zs f s)) = aM m ∧
      uAvg (fun f : Qubits m → ℤˣ => Zs f s * Real.sin (Zs f s)) = bM m ∧
      1 / 2 ≤ cM m ∧ cM m ≤ Real.exp (-(1 / 2)) ∧
      0 ≤ aM m ∧ aM m ≤ 1 / (3 * bigM m) ∧
      (1 - 1 / (6 * bigM m)) * Real.exp (-(1 / 2)) ≤ bM m ∧ bM m ≤ 1 ∧
      aM m - cM m ≤ -(5 / 12)) ∧
    Filter.Tendsto cM Filter.atTop (nhds (Real.exp (-(1 / 2)))) ∧
    Filter.Tendsto aM Filter.atTop (nhds 0) ∧
    Filter.Tendsto bM Filter.atTop (nhds (Real.exp (-(1 / 2)))) := by sorry

end QuarticGap
