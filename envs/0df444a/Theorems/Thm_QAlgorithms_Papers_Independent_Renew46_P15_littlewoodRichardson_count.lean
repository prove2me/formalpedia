-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P15_littlewoodRichardson_count
-- name    : QAlgorithms.Papers.Independent.Renew46.P15.littlewoodRichardson_count
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T20:14:18.775226+00:00
-- url     : https://prove2.me/theorems/349bf427-b881-4ffc-977e-af238ef9eb12
-- title:
--   GT Littlewood–Richardson acceptance and multiplicities
-- statement:
--   Fix an integer $N\ge2$ and two arbitrary finite-dimensional irreducible representations $S,S^\prime$ of $\mathrm{SU}(N)$, with normalized weakly decreasing integral top rows ending in zero. Use their orthonormal Gelfand–Tsetlin (GT) bases, without normalizing lower rows, and the real CG coefficients intertwining the common complexified Lie-algebra generators. These same coefficients apply to $\mathrm{SL}(N,\mathbb C)$.
--
--   For a GT-pattern $M=(m_{k,l})$ of $S$, put $b_{k,l}=m_{k,l}-m_{k,l-1}$, taking $m_{k,l-1}=0$ when $k=l$. Let $B_{0,l}=S^\prime_l$ and $B_{k,l}=S^\prime_l+\sum_{j=1}^k b_{j,l}$. Starting from $S^\prime$, process the positions $(k,l)$ with $k$ increasing and $l=N,N-1,\ldots,k$, adding $b_{k,l}$ to trial coordinate $l$. Accept $M$ exactly when every intermediate trial row remains weakly decreasing. Equivalently, for every $1\le k\le l\le N$,
--
--   $$
--    B_{k-1,1}\ge\cdots\ge B_{k-1,l-1}\ge B_{k,l}\ge\cdots\ge B_{k,N}.
--   $$
--
--   The initial segment is empty at $l=1$. Let $F(M)_l=B_{l,l}$ and normalize a final row by subtracting its last entry from every coordinate. For every normalized output label $T$,
--
--   $$
--    N_{S,S^\prime}^{T}=\#\{M:\ M\text{ is accepted and }F(M)-F(M)_N(1,\ldots,1)=T\}.
--   $$
--
--   This count is unchanged by exchanging the two inputs. Multiplicity on the left counts all copies of $T$ in any real orthogonal CG decomposition; no such decomposition is an input to the pattern-counting procedure. The result identifies all summands and their outer multiplicities.
-- source:
--   A numerical algorithm for the explicit calculation of SU(N) and SL(N,C) Clebsch-Gordan coefficients, arXiv:1009.0437v2, PDF p. 9, §VIII, Eq.(31), Appendix B

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P15

noncomputable section

open scoped BigOperators Matrix

namespace QAlgorithms.Papers.Independent.Renew46.P15

attribute [local instance] Classical.propDecidable

/-- VIII, Appendix B, PDF pp.9-10,15-16: individual-pattern chain acceptance
and complete multiplicity count, aggregating normalized outputs only at the end.
The arbitrary CG table identifies actual multiplicities; the counting algorithm
itself depends only on the two top rows. Corrects the repeated summation index
in printed B(k,l) using VIII steps 1-5 and Appendix B. -/
theorem littlewoodRichardson_count {n r : ℕ} (s sPrime : GTTopRow n)
    (t : Fin r → GTTopRow n) (c : CGTable s sPrime t) :
    (∀ m : Pattern s, lrAccepted m sPrime ↔
      ∀ k l : ℕ, k ≤ l → l < n + 2 → Antitone (lrChainWeight m sPrime k l)) ∧
    (∀ u : GTTopRow n, lrMultiplicity s sPrime u = outerMultiplicity t u) ∧
    (∀ u : GTTopRow n, lrMultiplicity s sPrime u = lrMultiplicity sPrime s u) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P15

end
