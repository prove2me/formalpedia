-- Prove2me | Theorems.Thm_SeqPostedPricing_MatroidSPM_span_isGreatest
-- name    : SeqPostedPricing.MatroidSPM.span_isGreatest
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T03:42:17.218283+00:00
-- url     : https://prove2.me/theorems/486e67b0-d536-4c0b-8fa0-72cee6a2109e
-- title:
--   §4.1: $\mathrm{span}(S)$ is the maximal $T\supseteq S$ with $\mathrm{rank}(T)=\mathrm{rank}(S)$
-- statement:
--   Let $\mathcal J$ be a matroid and $S\subseteq[n]$. Then
--
--   1. $S\subseteq\mathrm{span}(S)$,
--   2. $\mathrm{rank}(\mathrm{span}(S))=\mathrm{rank}(S)$, and
--   3. every $T\supseteq S$ with $\mathrm{rank}(T)=\mathrm{rank}(S)$ satisfies $T\subseteq\mathrm{span}(S)$,
--
--   where $\mathrm{span}(S)=\{e:\mathrm{rank}(S\cup\{e\})=\mathrm{rank}(S)\}$. So the maximal set in the paper's definition of the span exists and equals this set.
--
--   Differences from the source:
--   - encoding: span(S) defined as the maximal set T ⊇ S with rank(T) = rank(S) → span(S) = {e | rank(S ∪ {e}) = rank(S)}, and this theorem states that it is that maximal set; reason: the maximal set's existence is a theorem, so the definition is element-wise and the paper's definition is the statement
--   - reading: S′ ⊂ S in the rank and B ⊂ A in heredity → ⊆; reason: as in the definition of rank: the largest feasible subset of S may be S
-- source:
--   Chawla, Hartline, Malec, Sivan, Multi-parameter Mechanism Design and Sequential Posted Pricing, arXiv:0907.2435v2, §4.1, unnumbered, p. 6

import Mathlib
import Definitions.Def_SeqPostedPricing_MatroidSPM_IsMatroid
import Definitions.Def_SeqPostedPricing_MatroidSPM_rank
import Definitions.Def_SeqPostedPricing_MatroidSPM_span

namespace SeqPostedPricing.MatroidSPM

/-- **The span of `S` is the maximal set `T ⊇ S` with `rank(T) = rank(S)`.**
Chawla, Hartline, Malec, Sivan, *Multi-parameter Mechanism Design and Sequential Posted Pricing*, arXiv:0907.2435v2, §4.1, unnumbered, p. 6 (PDF p. 8): "The span of a set S ⊆ [n], span(S), is the maximal set
T ⊇ S with rank(T) = rank(S)."

For a matroid `J` and any set `S`: `S ⊆ span(S)`, `rank(span(S)) = rank(S)`, and every `T ⊇ S`
with `rank(T) = rank(S)` is contained in `span(S)`. So the maximal set of the paper's definition
exists and is the element-wise span `span(S) = {e | rank(S ∪ {e}) = rank(S)}`.

**Formalization Note.** `span` is defined by the element-wise test; this theorem is the
paper's definition. All three properties are stated together. -/
theorem span_isGreatest {n : ℕ} (Feas : Finset (Fin n) → Prop) (hmat : IsMatroid Feas)
    (S : Finset (Fin n)) :
    S ⊆ span Feas S ∧ rank Feas (span Feas S) = rank Feas S ∧
      ∀ T : Finset (Fin n), S ⊆ T → rank Feas T = rank Feas S → T ⊆ span Feas S := by sorry

end SeqPostedPricing.MatroidSPM
