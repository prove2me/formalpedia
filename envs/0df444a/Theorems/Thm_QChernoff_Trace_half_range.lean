-- Prove2me | Theorems.Thm_QChernoff_Trace_half_range
-- name    : QChernoff.Trace.half_range
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T09:26:27.030796+00:00
-- url     : https://prove2.me/theorems/0a917514-bff9-49b5-beb5-c43abdcb5229
-- title:
--   Proof of Theorem 1, p. 3 — $\operatorname{Tr}[a-a^sb^{1-s}]\le\operatorname{Tr}[(a-b)_+]=\operatorname{Tr}[(a-b)+|a-b|]/2$ for $0\le s\le 1/2$
-- statement:
--   Let $H$ be a complex Hilbert space, $a,b\ge0$ positive trace-class operators on $H$, and $0\le s\le\tfrac12$. Then
--
--   $$\operatorname{Tr}\big[a-a^{s}b^{1-s}\big]\ \le\ \operatorname{Tr}\big[(a-b)_+\big]\ =\ \operatorname{Tr}\big[(a-b)+|a-b|\big]/2 ,$$
--
--   with $a^0=\Pi_a$ the support projection at $s=0$, $(a-b)_+$ the positive part and $|a-b|=((a-b)^*(a-b))^{1/2}$.
--
--   Subtracting both sides from $\operatorname{Tr}[a]$ gives Theorem 1 for $0\le s\le1/2$; the case $1/2\le s\le1$ follows by exchanging $a$ and $b$.
--
--   **Formalization Note** $H$ is a complex Hilbert space of arbitrary dimension; operators are continuous linear maps $H\to H$ and $A\ge 0$ is the Loewner order of Mathlib. Trace class and the trace are the platform definitions `IsModulusTraceClass` (summability of $\langle e_i,|T|e_i\rangle$ over a fixed Hilbert basis) and `basisOperatorTrace` ($\sum_i\langle e_i,Te_i\rangle$) of `QAlgorithms_Papers_Independent_Next46_P02`, with scalar field $\mathbb C$. Inequalities between traces are in the partial order of $\mathbb C$, so they also assert that the two sides have the same imaginary part (both are real).
--
--   Differences from the source:
--   - generalization: positive operators of unspecified dimension (matrices in the paper's computations) → bounded operators on an arbitrary complex Hilbert space H, with no finite-dimensionality or separability assumption; reason: p. 3 states that the proof goes through in infinite dimensions; the case H = ℂⁿ is the matrix statement, so every instance of the source is an instance of the Lean statement
--   - encoding: Tr of the products formed from the positive operators a, b → a, b trace class (IsModulusTraceClass) and Tr the basis sum basisOperatorTrace; reason: the hypotheses exclude only operators whose traces in the statement are undefined; in finite dimension every operator is trace class, so no instance of the matrix statement is lost
--   - encoding: ≥ between the (real) traces → ≤ in the partial order of ℂ (ComplexOrder); reason: the traced quantities are real; ComplexOrder asserts that the real parts compare and the imaginary parts are equal, which implies the source's inequality
--   - reading: the zeroth power A⁰ of a possibly singular positive operator (not defined in the paper) → qPow A 0 = supportProj A, the orthogonal projection onto the closure of the range of A; reason: the paper's own use on p. 4 (for pure ρ₁ = |ψ⟩⟨ψ| the s = 0 value of Tr ρ₁^s ρ₂^{1−s} is ⟨ψ|ρ₂|ψ⟩); it is the stronger of the two readings, since Tr[Π_A B] ≤ Tr[B] makes the bound with A⁰ = 1 a consequence
-- source:
--   Audenaert et al., The Quantum Chernoff Bound, arXiv:quant-ph/0610027v1, p. 3, proof of Theorem 1 (display before "Subtracting both sides from Tr[a]")

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P02
import Definitions.Def_QChernoff_Trace_Power
open scoped ComplexOrder
open QAlgorithms.Papers.Independent.Next46.P02

namespace QChernoff.Trace

/-- Proof of Theorem 1, p. 3: `Tr[a − a^s b^{1−s}] ≤ Tr[(a − b)₊] = Tr[(a − b) + |a − b|]/2`
for positive trace-class `a, b` and `0 ≤ s ≤ 1/2`. -/
theorem half_range {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (a b : H →L[ℂ] H) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hatr : IsModulusTraceClass a) (hbtr : IsModulusTraceClass b)
    (s : ℝ) (hs0 : 0 ≤ s) (hs : s ≤ 1 / 2) :
    basisOperatorTrace (a - qPow a s * qPow b (1 - s)) ≤ basisOperatorTrace (a - b)⁺ ∧
      basisOperatorTrace (a - b)⁺ = basisOperatorTrace ((a - b) + CFC.abs (a - b)) / 2 := by sorry

end QChernoff.Trace
