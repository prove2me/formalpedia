-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P26_localTau
-- name    : QAlgorithms.Papers.Independent.Intake100.P26.localTau
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T17:21:04.900034+00:00
-- url     : https://prove2.me/theorems/c5871485-f600-4798-b87b-6697953ea00f
-- title:
--   Local tau operators on generalized weight spaces
-- statement:
--   Let $R$ be a finite reduced irreducible crystallographic root system of positive rank, with a fixed positive system and simple roots $\alpha_i$, Weyl group $W$, and full weight lattice $P$. Fix $q\in\mathbb C^\times$ which is not a root of unity. Write $\widetilde H$ for its affine Hecke algebra with $T_i^2=(q-q^{-1})T_i+1$ and the Bernstein relation with denominator $1-X^{-\alpha_i}$ interpreted as a Laurent-polynomial divided difference. Let $T=\operatorname{Hom}(P,\mathbb C^\times)$, with $(wt)(X^\lambda)=t(X^{w^{-1}\lambda})$. All modules below are finite dimensional complex left modules. Irreducible modules are nonzero.
--
--   Let $M$ be such a module and $t\in T$ satisfy $t(X^{\alpha_i})\ne1$. Write $M_t^{\rm gen}$ for its simultaneous generalized weight space. On this space define $\tau_i=T_i-(q-q^{-1})(1-X^{-\alpha_i})^{-1}$, where the inverse is an operator on the generalized weight space.
--
--   Then $\tau_i$ maps $M_t^{\rm gen}$ into $M_{s_it}^{\rm gen}$ and, on $M_t^{\rm gen}$,
--   $$X^\lambda\tau_i=\tau_iX^{s_i\lambda},\qquad \tau_i\tau_i=\frac{(q-q^{-1}X^{\alpha_i})(q-q^{-1}X^{-\alpha_i})}{(1-X^{\alpha_i})(1-X^{-\alpha_i})}.$$
--   If $M_t^{\rm gen}\ne0$, both directed tau maps are bijective if and only if $t(X^{\alpha_i})\notin\{q^2,q^{-2}\}$. For $i\ne j$, the two alternating tau words with $m_{ij}=\operatorname{ord}(s_is_j)$ factors agree whenever every factor is defined at its incoming weight. Products act rightmost first.
--
--   This describes the local operators without replacing Jordan operators by their eigenvalues. The nonzero-space guard repairs the printed invertibility equivalence on zero spaces; the second braid word is corrected to alternate $j,i,j,\ldots$.
-- source:
--   Calibrated representations of affine Hecke algebras, arXiv:math/0401323v2, PDF p. 7, Proposition 2.7(a)–(e)

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P26

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P26

open scoped BigOperators

variable {D : Datum} {V U : Type*}

variable [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U]

/-- Proposition 2.7(a)--(e), PDF pp.7--9. The iff in (d) is restricted to a
nonzero generalized space, repairing the zero-dimensional determinant edge.
The second braid word alternates j,i,j, correcting the printed j,i,i. -/
theorem localTau (D : Datum) (q : ℂ) (hq : GoodParameter q)
    (A : HeckeGenerators D V) [FiniteDimensional ℂ V] (hA : Relations q A)
    (t : Torus D) (i : Fin D.rank) (hi : torusCharacterEval t (simpleRootWeight D i) ≠ 1) :
    Set.MapsTo (localIntertwiner q A t i) (genSpace A t) (genSpace A (weylCharacter D (simple D i) t)) ∧
    (∀ x m, m ∈ genSpace A t →
      A.X x (localIntertwiner q A t i m) = localIntertwiner q A t i (A.X (simple D i • x) m)) ∧
    (∀ m, m ∈ genSpace A t →
      localIntertwiner q A (weylCharacter D (simple D i) t) i (localIntertwiner q A t i m) = tauSquare q A t i m) ∧
    (genSpace A t ≠ ⊥ →
      ((Set.BijOn (localIntertwiner q A t i) (genSpace A t) (genSpace A (weylCharacter D (simple D i) t)) ∧
        Set.BijOn (localIntertwiner q A (weylCharacter D (simple D i) t) i)
          (genSpace A (weylCharacter D (simple D i) t)) (genSpace A t)) ↔
        torusCharacterEval t (simpleRootWeight D i) ≠ q ^ 2 ∧ torusCharacterEval t (simpleRootWeight D i) ≠ (q⁻¹) ^ 2)) ∧
    (∀ j : Fin D.rank, i ≠ j →
      TauWordDefined D t (alternating i j (braidLength D i j)) →
      TauWordDefined D t (alternating j i (braidLength D i j)) →
      ∀ m, m ∈ genSpace A t →
        tauWord q A t (alternating i j (braidLength D i j)) m =
        tauWord q A t (alternating j i (braidLength D i j)) m) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P26

end
