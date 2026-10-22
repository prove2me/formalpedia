-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P33_lemma1
-- name    : QAlgorithms.Papers.Independent.Claimed50.P33.lemma1
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T12:36:11.153978+00:00
-- url     : https://prove2.me/theorems/7da5ab23-7bfa-4740-b2cd-c64f0fc2af07
-- title:
--   Lemma 1: tripartite seven-register decompositions
-- statement:
--   Let $A,A',B,B',C,C',E$ be disjoint finite registers of any normalized quantum state. The total correlation $I$ and dual correlation $S_3$, conditioned by entropy subtraction and measured in bits, satisfy
--
--   $$\begin{aligned}
--   I(AA':BB':CC'\mid E)&=I(A:B:C\mid A'B'C'E)+I(A':B':C'\mid E)\\
--   &\quad+I(A:B'C'\mid A'E)+I(B:A'C'\mid B'E)+I(C:A'B'\mid C'E),\\
--   S_3(AA':BB':CC'\mid E)&=S_3(A:B:C\mid A'B'C'E)+S_3(A':B':C'\mid E)\\
--   &\quad+I(AB:C'\mid A'B'E)+I(AC:B'\mid A'C'E)+I(BC:A'\mid B'C'E).
--   \end{aligned}$$
--
--   No independence is assumed. The distinct residual conditioning sets are essential to the superadditivity argument.
-- source:
--   Squashed entanglement for multipartite states and entanglement measures based on the mixed convex roof, arXiv:0704.2236v3, PDF p. 5, Lemma 1: tripartite seven-register decompositions

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P33

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P33

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Lemma 1, PDF pp.5–6,(38),(39). The seven disjoint sets are
A,A',B,B',C,C',E. Each residual term has its own conditioning set. -/
theorem lemma1 {n : ℕ} {D : Fin n → Type} [∀ i, Fintype (D i)]
    [∀ i, Nonempty (D i)] (rho : Matrix (RegisterBasis D) (RegisterBasis D) ℂ)
    (hrho : IsDensityMatrix rho) (a ap b bp c cp e : Finset (Fin n))
    (hdis : DisjointRegisters ![a,ap,b,bp,c,cp] e) :
    (info .total rho ![a ∪ ap,b ∪ bp,c ∪ cp] e =
      info .total rho ![a,b,c] (ap ∪ bp ∪ cp ∪ e) +
      info .total rho ![ap,bp,cp] e +
      info .total rho ![a,bp ∪ cp] (ap ∪ e) +
      info .total rho ![b,ap ∪ cp] (bp ∪ e) +
      info .total rho ![c,ap ∪ bp] (cp ∪ e)) ∧
    (info .dual rho ![a ∪ ap,b ∪ bp,c ∪ cp] e =
      info .dual rho ![a,b,c] (ap ∪ bp ∪ cp ∪ e) +
      info .dual rho ![ap,bp,cp] e +
      info .total rho ![a ∪ b,cp] (ap ∪ bp ∪ e) +
      info .total rho ![a ∪ c,bp] (ap ∪ cp ∪ e) +
      info .total rho ![b ∪ c,ap] (bp ∪ cp ∪ e)) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P33

end
