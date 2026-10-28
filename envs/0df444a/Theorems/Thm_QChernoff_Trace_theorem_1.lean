-- Prove2me | Theorems.Thm_QChernoff_Trace_theorem_1
-- name    : QChernoff.Trace.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T09:26:27.503+00:00
-- url     : https://prove2.me/theorems/84f95c10-da8a-45ca-a7a0-fd4cc797ca5a
-- title:
--   Theorem 1, p. 2, eq. (4) — $\operatorname{Tr}[A^sB^{1-s}]\ge\operatorname{Tr}[A+B-|A-B|]/2$ for positive trace-class $A,B$ and $0\le s\le1$
-- statement:
--   Let $H$ be a complex Hilbert space and let $A,B\ge0$ be positive trace-class operators on $H$. Then for every $0\le s\le1$,
--
--   $$\operatorname{Tr}\big[A^{s}B^{1-s}\big]\ \ge\ \frac{\operatorname{Tr}\big[A+B-|A-B|\big]}{2},$$
--
--   where $|A-B|=((A-B)^*(A-B))^{1/2}$, $A^s$ is the functional-calculus power for $s>0$, and $A^0=\Pi_A$ is the projection onto the support of $A$ (so the endpoint $s=0$ reads $\operatorname{Tr}[\Pi_AB]\ge\cdots$ and $s=1$ reads $\operatorname{Tr}[A\Pi_B]\ge\cdots$).
--
--   Applied to $A=\pi_1\rho_1^{\otimes n}$ and $B=\pi_0\rho_0^{\otimes n}$, the right-hand side is the minimal error probability of discriminating $n$ copies of two quantum states, and the inequality yields the upper bound $\xi_{QCB}\le-\log\min_{0\le s\le1}\operatorname{Tr}[\rho_0^s\rho_1^{1-s}]$ on the quantum Chernoff exponent; together with the lower bound of Nussbaum and Szkoła it identifies the exponent.
--
--   **Formalization Note** $H$ is a complex Hilbert space of arbitrary dimension; operators are continuous linear maps $H\to H$ and $A\ge 0$ is the Loewner order of Mathlib. Trace class and the trace are the platform definitions `IsModulusTraceClass` (summability of $\langle e_i,|T|e_i\rangle$ over a fixed Hilbert basis) and `basisOperatorTrace` ($\sum_i\langle e_i,Te_i\rangle$) of `QAlgorithms_Papers_Independent_Next46_P02`, with scalar field $\mathbb C$. Inequalities between traces are in the partial order of $\mathbb C$, so they also assert that the two sides have the same imaginary part (both are real).
--
--   Differences from the source:
--   - generalization: positive operators of unspecified dimension (matrices in the paper's computations) → bounded operators on an arbitrary complex Hilbert space H, with no finite-dimensionality or separability assumption; reason: p. 3 states that the proof goes through in infinite dimensions; the case H = ℂⁿ is the matrix statement, so every instance of the source is an instance of the Lean statement
--   - encoding: Tr of the products formed from the positive operators A, B → A, B trace class (IsModulusTraceClass) and Tr the basis sum basisOperatorTrace; reason: the hypotheses exclude only operators whose traces in the statement are undefined; in finite dimension every operator is trace class, so no instance of the matrix statement is lost
--   - encoding: ≥ between the (real) traces → ≤ in the partial order of ℂ (ComplexOrder); reason: the traced quantities are real; ComplexOrder asserts that the real parts compare and the imaginary parts are equal, which implies the source's inequality
--   - reading: the zeroth power A⁰ of a possibly singular positive operator (not defined in the paper) → qPow A 0 = supportProj A, the orthogonal projection onto the closure of the range of A; reason: the paper's own use on p. 4 (for pure ρ₁ = |ψ⟩⟨ψ| the s = 0 value of Tr ρ₁^s ρ₂^{1−s} is ⟨ψ|ρ₂|ψ⟩); it is the stronger of the two readings, since Tr[Π_A B] ≤ Tr[B] makes the bound with A⁰ = 1 a consequence
-- source:
--   Audenaert et al., The Quantum Chernoff Bound, arXiv:quant-ph/0610027v1, p. 2, Theorem 1, eq. (4)

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P02
import Definitions.Def_QChernoff_Trace_Power
open scoped ComplexOrder
open QAlgorithms.Papers.Independent.Next46.P02

namespace QChernoff.Trace

/-- Theorem 1, p. 2, eq. (4): `Tr[A^s B^{1−s}] ≥ Tr[A + B − |A − B|]/2` for positive
trace-class `A, B` on a complex Hilbert space and all `0 ≤ s ≤ 1` (zeroth power = support
projection; `≥` in the partial order of `ℂ`). -/
theorem theorem_1 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A B : H →L[ℂ] H) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hAtr : IsModulusTraceClass A) (hBtr : IsModulusTraceClass B)
    (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    basisOperatorTrace (A + B - CFC.abs (A - B)) / 2 ≤
      basisOperatorTrace (qPow A s * qPow B (1 - s)) := by sorry

end QChernoff.Trace
