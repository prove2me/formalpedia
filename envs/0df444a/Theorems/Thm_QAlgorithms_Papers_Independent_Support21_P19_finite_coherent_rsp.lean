-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P19_finite_coherent_rsp
-- name    : QAlgorithms.Papers.Independent.Support21.P19.finite_coherent_rsp
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T05:06:37.143616+00:00
-- url     : https://prove2.me/theorems/b2ca6907-450d-4250-a4b1-7de674fb812d
-- title:
--   Finite coherent RSP construction with returned entanglement
-- statement:
--   There is a universal constant $K>0$ such that for every integer $d\ge2$ and $0<\varepsilon<1$, one can choose an integer $n\ge1$ and fixed unitaries $R_1,\ldots,R_n$ with $n\le Kd\log_2(d)/\varepsilon^2$ and, uniformly for all normalized $d$-dimensional pure states $\psi$,
--
--   $$
--   (1-\varepsilon/2)I\le\frac dn\sum_kR_k|\psi\rangle\langle\psi|R_k^\dagger\le(1+\varepsilon/2)I.
--   $$
--
--   Define the effects $A_k=\frac{d}{n(1+\varepsilon/2)}(R_k|\psi\rangle\langle\psi|R_k^\dagger)^T$ and $A_{\rm fail}=I-\sum_k A_k$. They form a POVM. Applying the coherent square-root instrument to the supplied $\Phi_d$ has failure probability $0\le p_{\rm fail}<\varepsilon$. Its normalized successful vector before the corrections is
--
--   $$
--   \frac1{\sqrt n}\sum_k\overline{R_k\psi}_A|k\rangle_{A'}(R_k\psi)_B.
--   $$
--
--   Alice's controlled transpose, one $n$-ary coherent message and Bob's fixed controlled inverse yield the exact conditional output $\Phi_n\otimes\psi$. The computed subnormalized successful density is $(1-p_{\rm fail})|\Phi_n\rangle\langle\Phi_n|\otimes|\psi\rangle\langle\psi|$. The unconditional output, including a fixed placeholder label on failure and no free success notification, is a density matrix within trace distance $\varepsilon$ of this ideal normalized product. A single sequential protocol family implements the computed unconditional output, charging one supplied $\Phi_d$ and one $n$-ary coherent call; all Bob operations are independent of $\psi$. This is a heralded finite construction with an unconditional approximate implementation, not an exact deterministic resource conversion.
-- source:
--   Coherent Communication of Classical Messages, arXiv:quant-ph/0307091v3, PDF p. 3, Finite coherent RSP construction with returned entanglement

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P19

noncomputable section

namespace QAlgorithms.Papers.Independent.Support21.P19

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.3, finite coherent RSP: a single fixed O(d log d/eps^2) randomizing family,
complete instrument, strict failure bound, actual conditional success vector, and returned
entanglement. The unconditional channel includes failure; no notification is free.
One n-ary coherent call is used, implementable with at most ceil(log2 n) binary cobits.
The supplied Phi_d is explicit; this is not a deterministic exact conversion. -/
theorem finite_coherent_rsp :
    ∃ K : ℝ, 0 < K ∧ ∀ d : ℕ, 2 ≤ d → ∀ eps : ℝ, 0 < eps → eps < 1 →
    ∃ n : ℕ, 0 < n ∧ (n : ℝ) ≤ K*d*Real.logb 2 d/eps^2 ∧
    ∃ R : Fin n → Matrix.unitaryGroup (Fin d) ℂ, Randomizes R eps ∧
    (∀ k0 : Fin n, ∃ v : Kind → ℕ, (∀ k, v k ≤ budget 1 1 0 0 0 0 0 0 k) ∧
      Sequential (D := {psi : EuclideanSpace ℂ (Fin d) // IsState psi})
        (rspLibrary d n) 1 1 n (n*d) v (fun psi => rspOutput R eps psi.1 k0)) ∧
    ∀ psi : EuclideanSpace ℂ (Fin d), IsState psi →
      IsPOVM (rspPOVM R eps psi) ∧
      0 ≤ rspFailureProbability R eps psi ∧ rspFailureProbability R eps psi < eps ∧
      (((Real.sqrt (1-rspFailureProbability R eps psi))⁻¹ : ℝ) : ℂ) •
        rspBefore R eps psi = rspDisplayed R psi ∧
      rspSuccess R eps psi =
        ((1-rspFailureProbability R eps psi : ℝ) : ℂ) • rspIdeal n psi ∧
      ∀ k0 : Fin n, IsDensityMatrix (rspUnconditional R eps psi k0) ∧
        traceDistance (rspUnconditional R eps psi k0) (rspIdeal n psi) ≤ eps := by sorry

end QAlgorithms.Papers.Independent.Support21.P19

end
