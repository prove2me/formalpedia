-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P31_supportReduction
-- name    : QAlgorithms.Papers.Independent.Bridge50.P31.supportReduction
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:01:27.659194+00:00
-- url     : https://prove2.me/theorems/0791f4cd-f247-4f95-aa6f-60900a1abec5
-- title:
--   §3 unnumbered: support reduction and recovery extension
-- statement:
--   Let $A\subseteq B(H)$ and $B\subseteq B(K)$ be concrete finite-dimensional unital complex $C^*$-algebras on nonzero representation spaces. Maps are complex linear, $\operatorname{Tr}$ is the unnormalized representation trace, and $T^*$ is the Hilbert–Schmidt adjoint for $\langle a,b\rangle=\operatorname{Tr}(a^*b)$. A density operator is positive with trace one. All inverses of singular positive operators below are support inverses.
--
--   Let $\mathcal S$ be a nonempty set of densities and assume $T^*$ is unital Schwarz. There is a finite convex combination $\rho$ of elements of $\mathcal S$ with $\operatorname{supp}\sigma\le p:=\operatorname{supp}\rho$ for every $\sigma\in\mathcal S$. Put $p_0=\operatorname{supp}T(\rho)$ and let $\widetilde T:pAp\to p_0Bp_0$ be the restriction. Then output supports lie under $p_0$, $\widetilde T^*(p_0)=p$, the corner adjoint is unital Schwarz, and $\widetilde T_\rho=T_\rho$ on $pAp$. If the latter is Schwarz, it is unital Schwarz with units $p,p_0$. Furthermore,
--   $$
--   T\text{ reversible for }\mathcal S\quad\Longleftrightarrow\quad
--   \widetilde T\text{ reversible for }\mathcal S.
--   $$
--   Every ambient recovery restricts to the two support corners. Every corner recovery $R_c$ extends on $B$ by
--   $$
--   R(b)=R_c(p_0bp_0)+\operatorname{Tr}(b(I-p_0))\rho.
--   $$
--   The extension has unital Schwarz adjoint and recovers the whole family; if $R_c$ is $n$-positive, so is the extension. The mixture belongs to the closed convex hull, so enlargement to that hull includes the faithful corner reference. Empty families are excluded only from the mixture assertion.
-- source:
--   Reversibility conditions for quantum operations, arXiv:1107.0453v2, PDF p. 9, §3 unnumbered: support reduction and recovery extension

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P31

noncomputable section

namespace QAlgorithms.Papers.Independent.Bridge50.P31

open Filter MeasureTheory Set

open scoped Matrix ComplexOrder ComplexConjugate BigOperators Topology

open QAlgorithms.Papers.Independent.Information100.P60 (Mat copies)

open QAlgorithms.Papers.Independent.Information100.P30 (MatrixMap)

open QAlgorithms.Papers.Independent.Dependency50.P28 (tr LE)

open QAlgorithms.Papers.Independent.Dependency50.P21
  (channelAdjoint spectralFunction petz relativeEntropy)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

open QAlgorithms.Papers.Independent.Next46.P23 (Supports matrixCommutant)

open QAlgorithms.Papers.Independent.Support50.P12
  (Alg AlgebraDensity AlgebraExtension PositiveOnConcreteAlgebra AlgebraTracePreserving
   AlgebraKPositive AlgebraCompletelyPositive supp spec cpow quasi hull modularSpec)

open QAlgorithms.Papers.Independent.Information100.P50 (OperatorMonotone)

open QAlgorithms.Papers.Independent.Frontier18.P17 (hs)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- PDF pp.9–10: support-covering FINITE mixture, intrinsic corner reduction,
and the explicit extension of every corner recovery, preserving n-positivity.
The family is nonempty precisely for the asserted convex-combination state. -/
theorem supportReduction [Nonempty I] [Nonempty J] (A : Alg I) (B : Alg J)
    (T : MatrixMap I J) (hmap : AlgebraExtension A B T)
    (hadj : UnitalSchwarzOn B 1 1 (channelAdjoint T))
    (S : Set (Mat I)) (hstates : ∀ sigma ∈ S, AlgebraDensity A sigma) (hnonempty : S.Nonempty) :
    ∃ rho : Mat I, FiniteMixture S rho ∧ AlgebraDensity A rho ∧ rho ∈ hull S ∧
      let p := supp rho
      let p0 := supp (T rho)
      let Tc : Mat I → Mat J := fun a => T (p * a * p)
      (∀ sigma ∈ S, Supports sigma rho ∧ Supports (T sigma) (T rho)) ∧
      (∀ a ∈ supportCorner A p, T a ∈ supportCorner B p0 ∧ Tc a = T a) ∧
      channelAdjoint Tc p0 = p ∧
      UnitalSchwarzOn (supportCorner B p0) p0 p (channelAdjoint Tc) ∧
      (∀ a ∈ supportCorner A p, stateDual Tc rho a = stateDual T rho a) ∧
      (SchwarzOn (supportCorner A p) (stateDual T rho) →
        UnitalSchwarzOn (supportCorner A p) p p0 (stateDual Tc rho)) ∧
      (FamilyReversible A B T S ↔ CornerReversible A B T S p p0) ∧
      (∀ R : MatrixMap J I, AlgebraExtension B A R →
        UnitalSchwarzOn A 1 1 (channelAdjoint R) →
        (∀ sigma ∈ S, R (T sigma) = sigma) →
        ∀ b ∈ supportCorner B p0, R b ∈ supportCorner A p) ∧
      (∀ Rc : MatrixMap J I, MapRanges (supportCorner B p0) (supportCorner A p) Rc →
        UnitalSchwarzOn (supportCorner A p) p p0 (channelAdjoint Rc) →
        (∀ sigma ∈ S, Rc (T sigma) = sigma) →
        ∃ R : MatrixMap J I, AlgebraExtension B A R ∧
          (∀ b ∈ B, R b = extendRecovery Rc p0 rho b) ∧
          UnitalSchwarzOn A 1 1 (channelAdjoint R) ∧
          (∀ sigma ∈ S, R (T sigma) = sigma) ∧
          ∀ n : ℕ, CornerKPositive B p0 Rc n → AlgebraKPositive B R n) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P31

end
