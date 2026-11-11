-- Prove2me | Theorems.Thm_SpanForestStream_Unrestricted_lemma_3_4
-- name    : SpanForestStream.Unrestricted.lemma_3_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:32:45.018212+00:00
-- url     : https://prove2.me/theorems/974486a1-33a1-48ae-8907-34e07abe34fa
-- title:
--   Lemma 3.4 — pointwise-error source encoding: I(S; M) = Ω(L log(2 + m/L) log(U/m))
-- statement:
--   There are absolute constants $C,\beta^*>0$ (and an absolute constant $c>0$ for the $\Omega$) with the following property. Let $L=\ln(1/\beta)$, $0<\beta<\beta^*$, $m\ge L$ and $U\ge Cm$. Let $S$ be uniform among the $m$-subsets of $[U]$, and let a message $M$ be generated from $S$ alone, independently of the query. Suppose a randomized decoder, given $M$ and any $T\subsetneq S$, outputs a member of $S\setminus T$ with error at most $\beta$ for every fixed pair $(S,T)$, the probability including the message and fresh decoder coins. Then
--   $$I(S;M)\ge c\,L\,\log_2(2+m/L)\,\log_2(U/m).\qquad(3.19)$$
--   The decoder may be randomized and may output a failure symbol, and the message length is unrestricted.
--
--   This is the source of the confidence term of the lower bound.
--
--   Differences from the source:
--   - encoding: Ω(·) → ∃ absolute c > 0, quantified with C and β*; reason: O/Ω as absolute constants
--   - encoding: a message generated from S; a total randomized decoder with a failure symbol; unrestricted message length → a kernel S ↦ law of M on an arbitrary type, and a kernel (M, T) ↦ law on Option [U] (none = failure); reason: a total output channel; any message type
--   - encoding: L = ln(1/β), other logarithms → natural log for L as printed, log₂ elsewhere; I in bits; reason: App. A: binary unless written ln
-- source:
--   Chao, Cen, Ma, Wang, Space-Optimal Algorithms for Spanning Forests in Dynamic Streams at Every Confidence Level, arXiv:2611.04365 (PDF sha256 00f5bb17…69c92), p. 20 (PDF 23), Lemma 3.4, Eq. (3.19)

import Mathlib
import Definitions.Def_SpanForestStream_Unrestricted_Info
import Definitions.Def_SpanForestStream_Unrestricted_Protocols

open scoped ENNReal

namespace SpanForestStream.Unrestricted

/-- Lemma 3.4 (pointwise-error source encoding): there are absolute `C, β*, c > 0` such that for
`0 < β < β*`, `L = ln(1/β) ≤ m` and `U ≥ C m`, if `S` is uniform among the `m`-subsets of `[U]`, a
message `M` is drawn from `S` alone, and a randomized decoder given `M` and any `T ⊊ S` outputs a
member of `S \ T` with error at most `β` for every fixed pair `(S, T)`, then
`I(S; M) ≥ c L log₂(2 + m/L) log₂(U/m)`. -/
theorem lemma_3_4 :
    ∃ C βstar c : ℝ, 0 < C ∧ 0 < βstar ∧ 0 < c ∧
      ∀ (β : ℝ) (m U : ℕ), 0 < β → β < βstar → Real.log (1 / β) ≤ m → C * m ≤ U →
      ∀ {Msg : Type} (msg : Finset (Fin U) → PMF Msg)
        (dec : Msg → Finset (Fin U) → PMF (Option (Fin U))),
        (∀ S T : Finset (Fin U), S.card = m → T ⊂ S →
          ((msg S).bind fun M => dec M T).toOuterMeasure {o | ¬ URSolves S T o} ≤
            ENNReal.ofReal β) →
        ENNReal.ofReal (c * Real.log (1 / β) * Real.logb 2 (2 + m / Real.log (1 / β)) *
            Real.logb 2 (U / m)) ≤
          mutualInfo ((uniformSubsets U m).bind fun S => (msg S).map fun M => (S, M))
            Prod.fst Prod.snd := by sorry

end SpanForestStream.Unrestricted
