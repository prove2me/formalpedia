-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P18_theorem_4_2
-- name    : QAlgorithms.Papers.Independent.Advance50.P18.theorem_4_2
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T11:46:27.339484+00:00
-- url     : https://prove2.me/theorems/94c3c31b-be6c-4886-b00b-df81283ae403
-- title:
--   Theorem 4.2: real product-state private channel
-- statement:
--   Let $B=\{\cos\theta|0\rangle+\sin\theta|1\rangle:0\le\theta<2\pi\}$ and let $S=B^{\otimes n}$ be exactly its set of tensor products. For $x\in\{0,2\}^n$, let $\bar\sigma_x$ be the tensor product of the corresponding $I$ and $Y$ operators. Choosing each such string uniformly gives an ancilla-free private quantum channel:
--
--   $$\sum_{x\in\{0,2\}^n}2^{-n}\bar\sigma_x|\psi\rangle\langle\psi|\bar\sigma_x^\dagger=I_{2^n}/2^n\quad(\psi\in B^{\otimes n}).$$
--
--   The Kraus coefficient is $2^{-n/2}$, and all keyed operations are reversible. This smaller key suffices for real product states; the statement makes no assertion for arbitrary real-amplitude entangled states.
-- source:
--   Private Quantum Channels and the Cost of Randomizing Quantum Information, arXiv:quant-ph/0003101v2, PDF p. 5, Theorem 4.2: real product-state private channel

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P18

namespace QAlgorithms.Papers.Independent.Advance50.P18

open scoped ComplexConjugate

noncomputable section

variable {K I A : Type*} [Fintype K] [DecidableEq K]
  [Fintype I] [DecidableEq I] [Fintype A] [DecidableEq A]

/-- PDF p.5, Theorem 4.2: the uniform tensor I/Y ensemble privatizes B tensor n. -/
theorem theorem_4_2 (n : ℕ) :
    BarePQC (realProductSource n) (realPauli n) (sourceMixedIdentity (Qubits n)) := by sorry

end

end QAlgorithms.Papers.Independent.Advance50.P18
