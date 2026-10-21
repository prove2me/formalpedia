-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P15_gtPattern_predecessor_index
-- name    : QAlgorithms.Papers.Independent.Renew46.P15.gtPattern_predecessor_index
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T20:18:04.06838+00:00
-- url     : https://prove2.me/theorems/689fc6fb-afbf-41ae-801c-03db600018ba
-- title:
--   GT predecessor and one-based matrix indexing
-- statement:
--   Fix $N\ge2$ and a normalized dominant integral top row $S$. Let $\mathcal G(S)$ be all integral GT-patterns with this top row, with unnormalized lower rows satisfying betweenness. Its cardinality is $\dim(S)$. Order positions from the top row to the bottom row and from left to right inside each row; use this position order for lexicographic comparison of patterns. Define
--
--   $$
--    Q(M)=1+\#\{M^\prime\in\mathcal G(S):M^\prime<M\}.
--   $$
--
--   The partial predecessor is absent at the minimal pattern. Otherwise find the last lower-row entry $m_{k,l}>m_{k+1,l+1}$, decrease it by one, retain all earlier entries and the top row, and reset every later entry to its new upper neighbor $\widetilde m_{k,l+1}$. This yields the immediate preceding valid pattern. Moreover $\mathcal G(S)$ is nonempty, $Q$ is injective, its image is exactly $\{1,\ldots,\dim(S)\}$, and it preserves and reflects strict order. The endpoint patterns satisfy
--
--   $$
--    Q(M_{\mathrm{low}})=1,\qquad Q(H)=\dim(S),
--    \qquad (M_{\mathrm{low}})_{k,l}=m_{k+N-l,N},\quad H_{k,l}=m_{k,N}.
--   $$
--
--   There are exactly $Q(M)-1$ successful predecessor steps before the predecessor is absent. This supplies matrix indices with the mathematical one-based convention, including the one-pattern trivial irrep.
-- source:
--   A numerical algorithm for the explicit calculation of SU(N) and SL(N,C) Clebsch-Gordan coefficients, arXiv:1009.0437v2, PDF p. 18, Appendix C.2, Eqs.(C7)–(C9)

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P15

noncomputable section

open scoped BigOperators Matrix

namespace QAlgorithms.Papers.Independent.Renew46.P15

attribute [local instance] Classical.propDecidable

/-- Appendix C.2, (C7)-(C9), PDF pp.17-18: predecessor validity, immediate
precedence, inclusive one-based enumeration and the extreme patterns. Q is one
plus the number of successful predecessor steps, correcting the omitted initial
pattern in the prose according to (C7), Table V and the endpoint sentence. -/
theorem gtPattern_predecessor_index {n : ℕ} (s : GTTopRow n) :
    0 < Fintype.card (Pattern s) ∧
    Function.Injective (patternRank (s := s)) ∧
    (∀ q : ℕ, (∃ m : Pattern s, patternRank m = q) ↔
      1 ≤ q ∧ q ≤ Fintype.card (Pattern s)) ∧
    (∀ a b : Pattern s, patternLt a b ↔ patternRank a < patternRank b) ∧
    (∀ m : Pattern s,
      (patternRank m = 1 ↔ ∀ (l k : Fin (n + 2)) (hkl : k ≤ l),
        patternGrid m l k = s.val ⟨k.val + (n + 1 - l.val), by
          have hl := l.isLt
          have hklNat : k.val ≤ l.val := hkl
          omega⟩) ∧
      (patternRank m = Fintype.card (Pattern s) ↔
        ∀ l k : Fin (n + 2), k ≤ l → patternGrid m l k = s.val k) ∧
      (match patternPredecessor m with
        | none => patternRank m = 1
        | some raw => ∃ p : Pattern s, patternGrid p = raw ∧
            patternRank m = patternRank p + 1 ∧
            ∀ q : Pattern s, patternLt q m → q = p ∨ patternLt q p) ∧
      HasPredecessorChain (patternRank m - 1) m ∧
      ∀ steps, HasPredecessorChain steps m → steps + 1 = patternRank m) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P15

end
