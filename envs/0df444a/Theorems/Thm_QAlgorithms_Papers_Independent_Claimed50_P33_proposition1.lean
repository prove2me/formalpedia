-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P33_proposition1
-- name    : QAlgorithms.Papers.Independent.Claimed50.P33.proposition1
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T12:32:57.50327+00:00
-- url     : https://prove2.me/theorems/08b09f2a-06bd-4642-a29b-d21b71a6007a
-- title:
--   Proposition 1: four identities and conditional additivity
-- statement:
--   Let $m\ge2$ and let $X,A_1,\ldots,A_m$ be disjoint finite registers of a normalized quantum state. Write $A_{<i}=A_1\cdots A_{i-1}$ and $A_{-i}=A_1\cdots A_{i-1}A_{i+1}\cdots A_m$. Entropies and informations are in bits; $I$ is total correlation and $S_m$ is its dual. Then
--
--   $$\begin{aligned}
--   I(XA_1:\cdots:A_m)&=I(A_1:\cdots:A_m\mid X)+\sum_{i=2}^m I(X:A_i),\\
--   &=I(A_1:\cdots:A_m)+\sum_{i=2}^m I(X:A_i\mid A_{<i}),\\
--   S_m(XA_1:\cdots:A_m)&=S_m(A_1:\cdots:A_m\mid X)+I(X:A_2\cdots A_m),\\
--   &=-I(A_2:\cdots:A_m)+\sum_{i=2}^m I(A_i:XA_{-i}).
--   \end{aligned}$$
--
--   For either information, conditional values add on independent products, conditioning a linear entropy expression successively on $E,E'$ is the same as conditioning on $EE'$, and a classical conditioning register recovers the probability-weighted average of the conditional states. The total conditional correlation also has its chain expansion $I(A_1:\cdots:A_m\mid E)=\sum_{i=2}^m I(A_i:A_{<i}\mid E)$. A one-party total correlation is zero.
--
--   These identities provide the algebraic substrate for the subsequent squashing statements.
-- source:
--   Squashed entanglement for multipartite states and entanglement measures based on the mixed convex roof, arXiv:0704.2236v3, PDF p. 3, Proposition 1: four identities and conditional additivity

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P33

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P33

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Proposition 1, PDF pp.3–4,(18)–(21), including conditional additivity,
conditioning associativity (16), chain expansion (17), and classical
expectation recovery. The displayed sums start at the SECOND party.
At two parties the remaining one-party total information is zero. -/
theorem proposition1 {n k : ℕ} {D : Fin n → Type} [∀ i, Fintype (D i)]
    [∀ i, Nonempty (D i)] (rho : Matrix (RegisterBasis D) (RegisterBasis D) ℂ)
    (hrho : IsDensityMatrix rho) (a : Fin (k+2) → Finset (Fin n))
    (x : Finset (Fin n)) (hdis : DisjointRegisters a x) :
    (info .total rho (attachFirst a x) ∅ = info .total rho a x +
      ∑ i ∈ Finset.univ.erase 0, info .total rho ![x,a i] ∅) ∧
    (info .total rho (attachFirst a x) ∅ = info .total rho a ∅ +
      ∑ i ∈ Finset.univ.erase 0, info .total rho ![x,a i] (earlierParties a i)) ∧
    (info .dual rho (attachFirst a x) ∅ = info .dual rho a x +
      info .total rho ![x,laterParties a] ∅) ∧
    (info .dual rho (attachFirst a x) ∅ =
      -info .total rho (fun i : Fin (k+1) => a i.succ) ∅ +
      ∑ i ∈ Finset.univ.erase 0,
        info .total rho ![a i,x ∪ (Finset.univ.erase i).biUnion a] ∅) ∧
    (∀ (m : ℕ) (D F : Fin m → Type) [∀ i, Fintype (D i)] [∀ i, Fintype (F i)]
      [∀ i, Nonempty (D i)] [∀ i, Nonempty (F i)]
      (E Z : Type) [Fintype E] [Fintype Z] [Nonempty E] [Nonempty Z]
      (r : Matrix (RegisterBasis D × E) (RegisterBasis D × E) ℂ)
      (s : Matrix (RegisterBasis F × Z) (RegisterBasis F × Z) ℂ),
      2 ≤ m → IsDensityMatrix r → IsDensityMatrix s → ∀ kind : InformationKind,
      conditionalMultipartiteInformation kind (pairedProduct r s) (singleParties m) ∅ =
        conditionalMultipartiteInformation kind r (singleParties m) ∅ + conditionalMultipartiteInformation kind s (singleParties m) ∅) ∧
    (∀ (j : ℕ) (c : Fin j → ℝ) (s : Fin j → Finset (Fin n))
      (e f : Finset (Fin n)),
      entropyExpression (trivialExtension rho) c s (e ∪ f) =
        twiceConditioned (trivialExtension rho) c s e f) ∧
    (∀ (m : ℕ) (a : Fin (m+2) → Finset (Fin n)) (e : Finset (Fin n)),
      DisjointRegisters a e → info .total rho a e =
        ∑ i ∈ Finset.univ.erase 0,
          info .total rho ![a i,earlierParties a i] e) ∧
    (∀ (ell : ℕ) (p : Fin ell → ℝ)
      (r : Fin ell → Matrix (RegisterBasis D) (RegisterBasis D) ℂ),
      (∀ j, 0 ≤ p j) → (∑ j, p j) = 1 → (∀ j, IsDensityMatrix (r j)) →
      ∀ kind : InformationKind,
      let cq : Matrix (RegisterBasis D × Fin ell) (RegisterBasis D × Fin ell) ℂ :=
        fun u v => if u.2 = v.2 then (p u.2 : ℂ) * r u.2 u.1 v.1 else 0
      conditionalMultipartiteInformation kind cq a ∅ = ∑ j, p j * info kind (r j) a ∅) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P33

end
