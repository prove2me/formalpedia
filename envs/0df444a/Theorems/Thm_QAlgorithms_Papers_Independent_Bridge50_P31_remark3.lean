-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P31_remark3
-- name    : QAlgorithms.Papers.Independent.Bridge50.P31.remark3
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T15:58:13.139987+00:00
-- url     : https://prove2.me/theorems/b8e7861d-692a-4a55-9e3e-c5b284a101d3
-- title:
--   Remark 3: faithful-family refinement
-- statement:
--   Let $A\subseteq B(H)$ and $B\subseteq B(K)$ be concrete finite-dimensional unital complex $C^*$-algebras on nonzero representation spaces. Maps are complex linear, $\operatorname{Tr}$ is the unnormalized representation trace, and $T^*$ is the Hilbert–Schmidt adjoint for $\langle a,b\rangle=\operatorname{Tr}(a^*b)$. A density operator is positive with trace one. All inverses of singular positive operators below are support inverses.
--
--   Let $\mathcal S$ be a set of density operators in $A$ containing an invertible $\rho$, with $\rho_0=T(\rho)$ invertible. Assume $T^*$ and the computed map
--   $$
--   T_\rho(a)=\rho_0^{-1/2}T(\rho^{1/2}a\rho^{1/2})\rho_0^{-1/2}
--   $$
--   are unital Schwarz maps. Reversibility means that one linear map $R:B\to A$, whose adjoint is unital Schwarz, satisfies $R(T(\sigma))=\sigma$ for every $\sigma\in\mathcal S$.
--
--   Assume every $\sigma\in\mathcal S$ is invertible. Reversibility is equivalent to Chernoff equality on $\mathcal S$ itself. If $\mathcal S_0\subseteq\mathcal S$, $\mathcal S\subseteq\overline{\operatorname{co}}(\mathcal S_0\cup\{\rho\})$ and $T(\rho)\notin\overline{T(\mathcal S_0)}$, put
--   $$
--   r_0=\inf_{\sigma\in\mathcal S_0}D(T(\rho)\Vert T(\sigma))>0
--   $$
--   when $\mathcal S_0$ is nonempty. Reversibility is equivalent to existence of one $r\in[0,r_0]$ for which $H_r(\sigma,\rho)=H_r(T(\sigma),T(\rho))$ for all $\sigma\in\mathcal S_0$. For $\mathcal S_0=\varnothing$, the hypotheses force $\mathcal S=\{\rho\}$ and any positive threshold works; the formal definition chooses $r_0=1$. These refinements remove the unnecessary convexification in Theorem 7.
-- source:
--   Reversibility conditions for quantum operations, arXiv:1107.0453v2, PDF p. 22, Remark 3: faithful-family refinement

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

/-- PDF p.22, Remark 3: faithful families need no convexification for Chernoff;
the extra Hoeffding test uses only S0, with the stated common entropy threshold. -/
theorem remark3 [Nonempty I] [Nonempty J] (A : Alg I) (B : Alg J) (T : MatrixMap I J)
    (S : Set (Mat I)) (rho : Mat I) (h : Conditions A B T S rho)
    (hfaith : ∀ sigma ∈ S, sigma.PosDef) :
    (FamilyReversible A B T S ↔ ∀ sigma ∈ S,
      QAlgorithms.Papers.Independent.Support50.P12.chernoff sigma rho =
        QAlgorithms.Papers.Independent.Support50.P12.chernoff (T sigma) (T rho)) ∧
    (∀ S0 : Set (Mat I), S0 ⊆ S → S ⊆ hull (S0 ∪ {rho}) → T rho ∉ closure (T '' S0) →
      0 < faithfulRate T rho S0 ∧
      (FamilyReversible A B T S ↔ ∃ r ∈ Icc (0 : ℝ) (faithfulRate T rho S0),
        ∀ sigma ∈ S0, QAlgorithms.Papers.Independent.Support50.P12.hoeffding sigma rho r = QAlgorithms.Papers.Independent.Support50.P12.hoeffding (T sigma) (T rho) r)) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P31

end
