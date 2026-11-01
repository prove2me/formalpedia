-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P03_amplification
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P03.amplification
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T03:52:56.307351+00:00
-- url     : https://prove2.me/theorems/7795309f-2944-4663-8967-b8f2bf4b5d51
-- title:
--   §2.4.1: independent repetition and majority amplification
-- statement:
--   Suppose a $Q$ circuit on a classical input computes a promised $m$-bit function with worst-case error at most $0<\epsilon<1/2$. Repeat it $r>0$ times on fresh memories with the same classical input, and return a strict majority, flagging the absence of a majority as failure. This computation has a circuit with gate count and work bounded by one polynomial in $r$ and the original circuit and register sizes. Its output law is exactly that of independent original outcomes followed by majority. For every valid input,
--
--   $$
--   \Pr[\text{error or failure}]\le\sum_{2j\ge r}\binom rj\epsilon^j(1-\epsilon)^{r-j}\le\lambda^r,
--   \qquad\lambda=2\sqrt{\epsilon(1-\epsilon)}<1.
--   $$
--
--   For every polynomial $t(n)$ and fixed $\epsilon$, a polynomially bounded positive repetition count makes $\lambda^{r(n)}\le e^{-t(n)}$.
--
--   The majority computation and fresh work are charged; the construction copies classical inputs and does not clone quantum states.
-- source:
--   Quantum measurements and the Abelian Stabilizer Problem, arXiv:quant-ph/9511026v1, PDF p. 11, §2.4.1: independent repetition and majority amplification

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P03

noncomputable section

open scoped Matrix ComplexConjugate Kronecker

namespace QAlgorithms.Papers.Independent.Intakethird100.P03

open QAlgorithms.Papers.Independent.Renew46.P01 (cleanVector)

attribute [local instance] Classical.propDecidable

/-- PDF p.11: independent repetition and charged majority computation, the explicit
binomial/exponential bound, and polynomial overhead for exp(-poly(n)) error. -/
theorem amplification :
    (∃ p : Polynomial ℕ, ∀ (n m w : ℕ) (c : Circuit kitaevGateBasis (n + w))
      (out : Fin m ↪ Fin (n + w)) (N : Set (Qubits n)) (F : Qubits n → Qubits m)
      (epsilon : ℝ), 0 < epsilon → epsilon < 1 / 2 →
      Computes c.unitary out N F epsilon → ∀ r : ℕ, 0 < r →
      ∃ (W : ℕ) (cmajority : Circuit kitaevGateBasis (n + W)) (outmajority : Fin (m + 1) ↪ Fin (n + W)),
        cmajority.size ≤ p.eval (r * (n + m + w + c.size + 1)) ∧
        W ≤ p.eval (r * (n + m + w + c.size + 1)) ∧
        (∀ x y, probEvent (act cmajority.unitary (inputState x W))
          (fun z => z ∘ outmajority = y) = repeatedMajorityLaw c.unitary out r x y) ∧
        (∀ x ∈ N, 1 - majorityTail r epsilon ≤
          probEvent (act cmajority.unitary (inputState x W))
            (fun z => z ∘ outmajority = Fin.snoc (F x) true)) ∧
        majorityTail r epsilon ≤ amplificationRate epsilon ^ r ∧
        amplificationRate epsilon < 1) ∧
    (∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 / 2 → ∀ t : Polynomial ℕ,
      ∃ (R : ℕ → ℕ) (p : Polynomial ℕ), ∀ n : ℕ,
        0 < R n ∧ R n ≤ p.eval n ∧
        amplificationRate epsilon ^ R n ≤ Real.exp (-((t.eval n : ℕ) : ℝ))) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P03

end
