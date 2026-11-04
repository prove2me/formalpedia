-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P18_pureState_marginalEntropy_eq
-- name    : QAlgorithms.Papers.Independent.Claimed50.P18.pureState_marginalEntropy_eq
-- status  : Proved
-- author  : @Alien60
-- created : 2026-11-02T20:15:58.789969+00:00
-- url     : https://prove2.me/theorems/a92dcc06-8b51-461e-bf7b-e7ca98c18114
-- title:
--   The two marginals of a pure bipartite state have equal entropy
-- statement:
--   Let $\mathcal H_I,\mathcal H_J$ be separable complex Hilbert spaces with countable orthonormal bases indexed by $I$ and $J$, and let $\psi=|arphiangle\langlearphi|$ be a pure state on $\mathcal H_I\otimes\mathcal H_J$ (with $\|arphi\|=1$). Then the von Neumann entropies of its two reduced states coincide:
--
--   $$
--   H(\operatorname{Tr}_J\psi)=H(\operatorname{Tr}_I\psi)\in[0,+\infty].
--   $$
--
--   By the Schmidt decomposition $arphi=\sum_k\sqrt{\lambda_k}\,e_k\otimes f_k$, both marginals have the same nonzero eigenvalues $(\lambda_k)$, so both entropies equal $-\sum_k\lambda_k\log\lambda_k$, finite or infinite. In the source this gives $H(AB)=H(C)$ for a pure state $ho_{ABC}$, which is how $H(C)<\infty$ makes all quantities in identities (3)-(4) finite.
--
--   **Formalization Note** $H$ is the frozen `homogeneousEntropy` of Frontier18.P01 (the directed supremum of the finite-dimensional homogeneous entropies $-\operatorname{Tr}X\log X+\operatorname{Tr}X\log\operatorname{Tr}X$ of finite coordinate compressions, valued in $[0,\infty]$), and the partial traces are the coefficientwise series `traceSecond` $(\operatorname{Tr}_J X)_{ii'}=\sum_{j}X_{(i,j),(i',j)}$ and `traceFirst` $(\operatorname{Tr}_I X)_{jj'}=\sum_{i}X_{(i,j),(i,j')}$. Pure states are the frozen `PureState` of Dependency50.P33 (rank-one $arphiarphi^*$ with $\|arphi\|=1$ in $\ell^2(I	imes J)$). Natural logarithms.
-- source:
--   Kuznetsova, Quantum conditional entropy for infinite-dimensional systems, arXiv:1004.4519v2, PDF p. 2, §1, identities (3)-(4) (step H(AB)=H(C) for pure rho_ABC); Schmidt decomposition: Nielsen--Chuang, Quantum Computation and Quantum Information, Theorem 2.7 and its corollary; Holevo--Shirokov arXiv:1004.2495v2 p.6

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P18

noncomputable section

open Filter

open scoped ENNReal BigOperators

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33

open QAlgorithms.Papers.Independent.Frontier18.P01

open QAlgorithms.Papers.Independent.Frontier18.P08 (operatorTrace)

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Claimed50.P18

theorem pureState_marginalEntropy_eq {I J : Type} [Countable I] [Countable J]
    (psi : PureState (I × J)) :
    homogeneousEntropy (traceSecond psi.val.coefficients) =
      homogeneousEntropy (traceFirst psi.val.coefficients) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P18

end
