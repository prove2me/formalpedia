-- Prove2me | Theorems.Thm_QChernoff_Trace_lemma_1
-- name    : QChernoff.Trace.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T09:26:23.895403+00:00
-- url     : https://prove2.me/theorems/a4150a74-26be-4599-894c-ab6a3edd71ef
-- title:
--   Lemma 1, p. 3, eq. (5) — $\operatorname{Tr}[PB(A^t-B^t)]\ge0$ for $0\le t\le1$, $P$ the projector on the range of $(A-B)_+$
-- statement:
--   Let $H$ be a complex Hilbert space, $A,B\ge0$ positive trace-class operators on $H$, and $0\le t\le1$. Let $P$ be the orthogonal projection onto the (closure of the) range of the positive part $(A-B)_+$. Then
--
--   $$\operatorname{Tr}\big[P\,B\,(A^{t}-B^{t})\big]\ \ge\ 0 .$$
--
--   Here $A^t$ is the functional-calculus power for $t>0$ and $A^0=\Pi_A$ is the support projection of $A$; at $t=0$ the statement reads $\operatorname{Tr}[PB(\Pi_A-\Pi_B)]\ge0$ and at $t=1$ it reads $\operatorname{Tr}[PB(A-B)]\ge0$.
--
--   Lemma 1 is the technical core of the proof of Theorem 1, which applies it to $a^{1-s}$, $b^{1-s}$ and $t=s/(1-s)$.
--
--   **Formalization Note** $H$ is a complex Hilbert space of arbitrary dimension; operators are continuous linear maps $H\to H$ and $A\ge 0$ is the Loewner order of Mathlib. Trace class and the trace are the platform definitions `IsModulusTraceClass` (summability of $\langle e_i,|T|e_i\rangle$ over a fixed Hilbert basis) and `basisOperatorTrace` ($\sum_i\langle e_i,Te_i\rangle$) of `QAlgorithms_Papers_Independent_Next46_P02`, with scalar field $\mathbb C$. Inequalities between traces are in the partial order of $\mathbb C$, so they also assert that the two sides have the same imaginary part (both are real).
--
--   Differences from the source:
--   - generalization: positive operators of unspecified dimension (matrices in the paper's computations) → bounded operators on an arbitrary complex Hilbert space H, with no finite-dimensionality or separability assumption; reason: p. 3 states that the proof goes through in infinite dimensions; the case H = ℂⁿ is the matrix statement, so every instance of the source is an instance of the Lean statement
--   - reading: positive operators A, B (no operator class named) → A, B positive and trace class (IsModulusTraceClass); Tr the basis sum basisOperatorTrace; reason: the operators are those of Theorem 1, positive with finite trace; trace class of B is what makes the traced product trace class, and trace class of the other operator is the class of Theorem 1 in which every trace of the paper's proof is defined; in finite dimension every operator is trace class
--   - encoding: ≥ between the (real) traces → ≤ in the partial order of ℂ (ComplexOrder); reason: the traced quantities are real; ComplexOrder asserts that the real parts compare and the imaginary parts are equal, which implies the source's inequality
--   - reading: P the projector on the range of (A − B)₊ → supportProj (A − B)⁺, the orthogonal projection onto the closure of the range; reason: in finite dimension the range is closed and the two agree; in infinite dimension the range of a compact operator need not be closed and the closure is the only orthogonal projection onto it
--   - reading: the zeroth power A⁰ of a possibly singular positive operator (not defined in the paper) → qPow A 0 = supportProj A, the orthogonal projection onto the closure of the range of A; reason: the paper's own use on p. 4 (for pure ρ₁ = |ψ⟩⟨ψ| the s = 0 value of Tr ρ₁^s ρ₂^{1−s} is ⟨ψ|ρ₂|ψ⟩); it is the stronger of the two readings, since Tr[Π_A B] ≤ Tr[B] makes the bound with A⁰ = 1 a consequence
-- source:
--   Audenaert et al., The Quantum Chernoff Bound, arXiv:quant-ph/0610027v1, p. 3, Lemma 1, eq. (5)

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P02
import Definitions.Def_QChernoff_Trace_Power
open scoped ComplexOrder
open QAlgorithms.Papers.Independent.Next46.P02

namespace QChernoff.Trace

/-- Lemma 1, p. 3, eq. (5). `P` is the projector on the (closure of the) range of `(A − B)₊`;
`qPow A 0` is the support projection of `A`. -/
theorem lemma_1 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A B : H →L[ℂ] H) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hAtr : IsModulusTraceClass A) (hBtr : IsModulusTraceClass B)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ basisOperatorTrace (supportProj (A - B)⁺ * B * (qPow A t - qPow B t)) := by sorry

end QChernoff.Trace
