-- Prove2me | Theorems.Thm_PrettyGoodCriterion_lemma_31
-- name    : PrettyGoodCriterion.lemma_31
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T08:29:17.537298+00:00
-- url     : https://prove2.me/theorems/7fdfa2ec-d6fd-42b3-8412-7f534f19985b
-- title:
--   Lemma 31 — gentle measurement: $\|A-PAP\|_1\le 2\sqrt{\operatorname{Tr}[A(I-P)]}$
-- statement:
--   Let $A$ be a **subnormalized state**, that is, a positive semidefinite $d\times d$ matrix with $\operatorname{Tr}A\le1$, and let $P$ be a $d\times d$ (orthogonal) projection. Then
--   $$\|A-PAP\|_1\le2\sqrt{\operatorname{Tr}[A(I-P)]},$$
--   where $\|X\|_1:=\operatorname{Tr}\sqrt{X^\dagger X}$ is the trace norm.
--
--   A projection that accepts the state with probability close to $1$ disturbs it little; this is used twice, with spectral projectors, in the proof of the strong converse (Theorem 7).
--
--   **Formalization Note** The trace norm is the published `WildeQIT.traceNorm`. $\operatorname{Tr}A$ and $\operatorname{Tr}[A(I-P)]$ are real for such $A,P$; real parts are taken.
--
--   Differences from the source:
--   - reading: P is a projection d × d matrix → P Hermitian and P * P = P; reason: an orthogonal projection: the paper's proof uses that P and I − P are projections with Tr(PA) ⩽ Tr(A), which needs 0 ⪯ P ⪯ I
--   - encoding: ℂ^d, d × d matrices → matrices indexed by an arbitrary finite type ι; reason: ℂ^d is the case ι = Fin d, and every finite type is Fin d up to relabelling, which changes no trace, product or positivity
--   - encoding: probabilities Tr(σ_x M_x̂) (and the other traces of products of positive semidefinite matrices) → real parts of the traces; reason: these traces are real; taking the real part changes no value
-- source:
--   Alrabiah, Guruswami, Binary code rate bounds via classical–quantum channels, arXiv:2608.09347 (held version, sha256 e6d5ac13…), Lemma 31, Appendix A, p.63 (PDF 65); definitions of subnormalized state and ‖·‖₁, p.63 (PDF 65); proof pp.63–64 (PDF 65–66)

import Mathlib
import Definitions.Def_WildeQIT_traceNorm

open scoped ComplexOrder

namespace PrettyGoodCriterion

/-- **Lemma 31 (Gentle measurement lemma)**, Alrabiah–Guruswami, arXiv:2608.09347 (held
version), Appendix A, p.63 (PDF 65); proof pp.63–64 (PDF 65–66).

If `A` is a subnormalized state (positive semidefinite with `Tr A ⩽ 1`, p.63) and `P` is a
projection, then `‖A − PAP‖₁ ⩽ 2 √(Tr[A(I − P)])`, where `‖X‖₁ := Tr √(X†X)` (p.63).

**Formalization Note.** Matrices are indexed by a finite type `ι` (the paper's `d × d`). A
projection is an orthogonal projection: Hermitian and idempotent. The trace norm is the published
`WildeQIT.traceNorm`, the real part of `Tr √(X†X)`; `Tr A` and `Tr[A(I − P)]` are real for such
`A, P`, and their real parts are taken. -/
theorem lemma_31 {ι : Type} [Fintype ι] [DecidableEq ι] (A P : Matrix ι ι ℂ)
    (hA : A.PosSemidef) (hA1 : A.trace.re ≤ 1) (hP : P.IsHermitian) (hPP : P * P = P) :
    WildeQIT.traceNorm (A - P * A * P) ≤ 2 * Real.sqrt (A * (1 - P)).trace.re := by sorry

end PrettyGoodCriterion
