-- Prove2me | Theorems.Thm_SeqHolevo_sen_union_bound
-- name    : SeqHolevo.sen_union_bound
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:59:31.524886+00:00
-- url     : https://prove2.me/theorems/d7750e3d-adf6-45ed-ad71-27162697a4e5
-- title:
--   Sen's non-commutative union bound (Lemma 3 of [12])
-- statement:
--   Let $\sigma$ be a subnormalized state ($\sigma\ge0$ and $\operatorname{Tr}\{\sigma\}\le1$) and let $\Pi_1,\dots,\Pi_N$ be orthogonal projectors on the same Hilbert space. Then
--
--   $$\operatorname{Tr}\{\sigma\}-\operatorname{Tr}\{\Pi_N\cdots\Pi_1\,\sigma\,\Pi_1\cdots\Pi_N\}\le2\sqrt{\sum_{i=1}^N\operatorname{Tr}\{(I-\Pi_i)\sigma\}} .$$
--
--   If each projector alone accepts $\sigma$ with high probability, the sequence of all of them does too, with a square-root loss. This is the key step of the error analysis of the sequential decoder.
--
--   Differences from the source:
--   - encoding: a subnormalized state σ on a Hilbert space → a positive trace-class coefficient array σ on ℓ²(J), any J, with Tr σ ≤ 1; reason: the same operators
--   - encoding: Tr{Π_N⋯Π_1 σ Π_1⋯Π_N} → realFockTracePair σ (Q† Q) with Q = projProd P N = Π_N⋯Π_1; reason: cyclicity of the trace: Tr{Q σ Q†} = Tr[σ Q†Q]
--   - encoding: projectors Π_1, …, Π_N → P 0, …, P (N−1) with IsOrthProjector; reason: 0-based relabelling; "projectors" in Sen's lemma are orthogonal projectors
--   - generalization: N ≥ 1 projectors → N = 0 allowed; reason: at N = 0 both sides are 0; the instances N ≥ 1 are the printed ones
--   - encoding: operators on a Hilbert space; Tr, ‖·‖₁ and the order ≤ → coefficient arrays on ℓ²(J) for any index type J; Tr[XE] = realFockTracePair X E; ‖·‖₁ = traceSize; ≤ = TraceOperatorLE (finite quadratic forms); reason: published coordinate conventions (Next46.P32, Dependency50.P33, Frontier18.P01); the same operators and numbers
-- source:
--   Wilde–Guha–Tan–Lloyd, Explicit capacity-achieving receivers for optical communication and quantum reading, arXiv:1202.0518v2, Appendix B, p.7 (Sen's non-commutative union bound, Lemma 3 of Ref. [12])

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P76
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P01
import Definitions.Def_SeqHolevo_idArr
import Definitions.Def_SeqHolevo_arrMul
import Definitions.Def_SeqHolevo_IsOrthProjector
import Definitions.Def_SeqHolevo_projProd

open QAlgorithms.Papers.Independent.Dependency50.P33 (IsTraceClass)
open QAlgorithms.Papers.Independent.Frontier18.P01 (IsPositive)
open QAlgorithms.Papers.Independent.Next46.P32 (realFockTracePair)

namespace SeqHolevo

/-- Wilde–Guha–Tan–Lloyd, *Explicit capacity-achieving receivers for optical communication and quantum reading*, arXiv:1202.0518v2, Appendix B, p.7 (PDF page): "Sen's non-commutative union bound (Lemma 3 of Ref. [12]),
which holds for any subnormalized state `σ` (`σ ≥ 0` and `Tr{σ} ≤ 1`) and sequence of
projectors `Π_1, ..., Π_N`:
`Tr{σ} − Tr{Π_N ⋯ Π_1 σ Π_1 ⋯ Π_N} ≤ 2 √(Σ_{i=1}^N Tr{(I − Π_i) σ})`."

**Formalization Note.** `σ` is a positive trace-class coefficient array on ℓ²(J), any `J`, with
`Tr σ ≤ 1`; the projectors are orthogonal (`IsOrthProjector`), given 0-based as `Π 0, …, Π (N−1)`
(the paper's `Π_1, …, Π_N`), and `N = 0` is allowed. With `Q = Π_N ⋯ Π_1 = projProd Π N`,
`Tr{Q σ Q†} = Tr[σ Q†Q]` (cyclicity), written `realFockTracePair σ (Q† Q)`;
`Tr σ = realFockTracePair σ I` and `Tr{(I − Π_i) σ} = realFockTracePair (I − Π_i) σ`. -/
theorem sen_union_bound {J : Type} (σ : Matrix J J ℂ) (hσ : IsPositive σ) (hσtr : IsTraceClass σ)
    (hσ1 : realFockTracePair σ (idArr J) ≤ 1) (N : ℕ) (P : ℕ → Matrix J J ℂ)
    (hP : ∀ i < N, IsOrthProjector (P i)) :
    realFockTracePair σ (idArr J) -
        realFockTracePair σ (arrMul (projProd P N).conjTranspose (projProd P N)) ≤
      2 * Real.sqrt (∑ i ∈ Finset.range N, realFockTracePair (idArr J - P i) σ) := by sorry

end SeqHolevo
