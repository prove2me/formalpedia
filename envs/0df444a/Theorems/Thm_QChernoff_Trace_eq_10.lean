-- Prove2me | Theorems.Thm_QChernoff_Trace_eq_10
-- name    : QChernoff.Trace.eq_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T09:26:29.042055+00:00
-- url     : https://prove2.me/theorems/8b93c42e-fa00-48c4-bdee-ab0981595919
-- title:
--   Eq. (10), p. 5 — $\operatorname{Tr}[PB(C+x)^{-1}\Delta(C+x)^{-1}]\ge0$, $P$ the projector on the range of $(C-B)_+$ (corrected: $C + x$ invertible)
-- statement:
--   Let $H$ be a complex Hilbert space, $B,C\ge0$ positive trace-class operators on $H$, $\Delta:=C-B$, and $P$ the orthogonal projection onto the (closure of the) range of $\Delta_+=(C-B)_+$. Let $x\ge0$ be a real number such that $C+x\mathbb 1$ is invertible (automatic when $x>0$). Then
--
--   $$\operatorname{Tr}\big[P\,B\,(C+x)^{-1}\,\Delta\,(C+x)^{-1}\big]\ \ge\ 0 .$$
--
--   With $C=B+t(A-B)$ this is the positivity of the inner integrand in the proof of Lemma 1, the key estimate of the paper.
--
--   **Formalization Note** $H$ is a complex Hilbert space of arbitrary dimension; operators are continuous linear maps $H\to H$ and $A\ge 0$ is the Loewner order of Mathlib. Trace class and the trace are the platform definitions `IsModulusTraceClass` (summability of $\langle e_i,|T|e_i\rangle$ over a fixed Hilbert basis) and `basisOperatorTrace` ($\sum_i\langle e_i,Te_i\rangle$) of `QAlgorithms_Papers_Independent_Next46_P02`, with scalar field $\mathbb C$. Inequalities between traces are in the partial order of $\mathbb C$, so they also assert that the two sides have the same imaginary part (both are real).
--
--   Differences from the source:
--   - generalization: positive operators of unspecified dimension (matrices in the paper's computations) → bounded operators on an arbitrary complex Hilbert space H, with no finite-dimensionality or separability assumption; reason: p. 3 states that the proof goes through in infinite dimensions; the case H = ℂⁿ is the matrix statement, so every instance of the source is an instance of the Lean statement
--   - reading: positive operators B, C (no operator class named) → B, C positive and trace class (IsModulusTraceClass); Tr the basis sum basisOperatorTrace; reason: the operators are those of Theorem 1, positive with finite trace; trace class of B is what makes the traced product trace class, and trace class of the other operator is the class of Theorem 1 in which every trace of the paper's proof is defined; in finite dimension every operator is trace class
--   - encoding: ≥ between the (real) traces → ≤ in the partial order of ℂ (ComplexOrder); reason: the traced quantities are real; ComplexOrder asserts that the real parts compare and the imaginary parts are equal, which implies the source's inequality
--   - reading: P the projector on the range of (A − B)₊ → supportProj (A − B)⁺, the orthogonal projection onto the closure of the range; reason: in finite dimension the range is closed and the two agree; in infinite dimension the range of a compact operator need not be closed and the closure is the only orthogonal projection onto it
--   - correction: x a non-negative scalar → x ≥ 0 with C + x·1 invertible (IsUnit); reason: for C = 0 and x = 0 the inverse (C + x)⁻¹ does not exist; the hypothesis holds for every x > 0 (the case used in Lemma 1) and keeps x = 0 for invertible C, where the paper's argument V⁻¹ ≥ ∆ + x still applies
-- source:
--   Audenaert et al., The Quantum Chernoff Bound, arXiv:quant-ph/0610027v1, p. 5, eq. (10), proof of Lemma 1, Appendix A

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P02
import Definitions.Def_QChernoff_Trace_Power
open scoped ComplexOrder
open QAlgorithms.Papers.Independent.Next46.P02

namespace QChernoff.Trace

/-- Eq. (10), p. 5 (corrected: `C + x` invertible). `P` is the projector on the (closure of
the) range of `(C − B)₊`, `Δ = C − B`. -/
theorem eq_10 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (B C : H →L[ℂ] H) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hBtr : IsModulusTraceClass B) (hCtr : IsModulusTraceClass C)
    (x : ℝ) (hx : 0 ≤ x) (hinv : IsUnit (C + (x : ℂ) • 1)) :
    0 ≤ basisOperatorTrace (supportProj (C - B)⁺ * B * Ring.inverse (C + (x : ℂ) • 1) *
      (C - B) * Ring.inverse (C + (x : ℂ) • 1)) := by sorry

end QChernoff.Trace
