-- Prove2me | Theorems.Thm_SeqHolevo_lemma_8
-- name    : SeqHolevo.lemma_8
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:58:42.446877+00:00
-- url     : https://prove2.me/theorems/c56a070c-f699-4d8a-a047-03c9d8be421f
-- title:
--   Lemma 8 (7) — substitution of states up to their trace distance
-- statement:
--   Let $\rho,\sigma$ be positive trace-class operators on a Hilbert space and let $\Lambda$ be an operator with $0\le\Lambda\le I$. Then
--
--   $$\operatorname{Tr}[\Lambda\rho]\le\operatorname{Tr}[\Lambda\sigma]+\|\rho-\sigma\|_1 ,$$
--
--   where $\|X\|_1=\operatorname{Tr}|X|$ is the trace norm. Two states can thus replace one another in the success probability of a test, at a cost of their trace distance. Appendix B uses it to replace $\varphi_{X^n(M)}$ by its projection $\Pi\varphi_{X^n(M)}\Pi$.
--
--   Differences from the source:
--   - reading: 0 ≤ ρ, σ (two states, per the preceding sentence) → IsPositive ρ, IsPositive σ and IsTraceClass ρ, IsTraceClass σ; reason: the lemma is about states ("Two states can substitute for one another"); in infinite dimensions Tr[Λρ] and ‖ρ − σ‖₁ need trace class
--   - generalization: ρ, σ ≤ I → no upper bound on ρ, σ; reason: Tr[Λ(ρ − σ)] ≤ ‖Λ‖ ‖ρ − σ‖₁ needs none; every pair with ρ, σ ≤ I is covered
--   - encoding: operators on a Hilbert space; Tr, ‖·‖₁ and the order ≤ → coefficient arrays on ℓ²(J) for any index type J; Tr[XE] = realFockTracePair X E; ‖·‖₁ = traceSize; ≤ = TraceOperatorLE (finite quadratic forms); reason: published coordinate conventions (Next46.P32, Dependency50.P33, Frontier18.P01); the same operators and numbers
-- source:
--   Wilde–Guha–Tan–Lloyd, Explicit capacity-achieving receivers for optical communication and quantum reading, arXiv:1202.0518v2, Appendix A, Lemma 8, eq. (7), p.6

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P76
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P01
import Definitions.Def_SeqHolevo_idArr

open QAlgorithms.Papers.Independent.Dependency50.P33 (IsTraceClass traceSize)
open QAlgorithms.Papers.Independent.Frontier18.P01 (IsPositive TraceOperatorLE)
open QAlgorithms.Papers.Independent.Next46.P32 (realFockTracePair)

namespace SeqHolevo

/-- Wilde–Guha–Tan–Lloyd, *Explicit capacity-achieving receivers for optical communication and quantum reading*, arXiv:1202.0518v2, Appendix A, Lemma 8, eq. (7), p.6 (PDF page): "Two states can substitute for one
another up to a penalty proportional to the trace distance between them: Lemma 8: Let
`0 ≤ ρ, σ, Λ ≤ I`. Then `Tr[Λρ] ≤ Tr[Λσ] + ‖ρ − σ‖₁`."

**Formalization Note.** Operators are coefficient arrays on ℓ²(J), any index type `J`.
`Tr[XE]` is the published `realFockTracePair X E = Re Σ_a Σ_b X_{ab} E_{ba}` (`Next46.P32`),
`‖·‖₁` the published trace norm `traceSize` (`Dependency50.P33`, finite on trace class), and
`0 ≤ ·`, `· ≤ I` the published Loewner order (`Frontier18.P01`). `ρ`, `σ` are required to be
positive and trace class (the lemma is about states); the printed bounds `ρ, σ ≤ I` are dropped
(a generalization: the inequality holds for all positive trace-class `ρ`, `σ`). -/
theorem lemma_8 {J : Type} (ρ σ Λ : Matrix J J ℂ)
    (hρ : IsPositive ρ) (hρtr : IsTraceClass ρ) (hσ : IsPositive σ) (hσtr : IsTraceClass σ)
    (hΛ : IsPositive Λ) (hΛI : TraceOperatorLE Λ (idArr J)) :
    realFockTracePair Λ ρ ≤ realFockTracePair Λ σ + (traceSize (ρ - σ)).toReal := by sorry

end SeqHolevo
