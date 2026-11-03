-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P18_generalizedRelativeEntropy_swapCoeff
-- name    : QAlgorithms.Papers.Independent.Claimed50.P18.generalizedRelativeEntropy_swapCoeff
-- status  : Proved
-- author  : @Alien60
-- created : 2026-11-02T20:15:49.551479+00:00
-- url     : https://prove2.me/theorems/45b0be01-12c9-43d0-8502-c83e29e96a4b
-- title:
--   Relative entropy is invariant under exchanging the tensor factors
-- statement:
--   Let $I,J$ be index sets and let $X,Y$ be coefficient arrays (operators in coordinates) on $\mathcal H_I\otimes\mathcal H_J$. Write $F:\mathcal H_I\otimes\mathcal H_J	o\mathcal H_J\otimes\mathcal H_I$ for the flip unitary $F(e_i\otimes f_j)=f_j\otimes e_i$. Then the (generalized, Lindblad) quantum relative entropy is invariant under the flip:
--
--   $$
--   D(FXF^*\,\|\,FYF^*)=D(X\|Y)\in[0,+\infty].
--   $$
--
--   This is the unitary invariance of relative entropy for the coordinate-permutation unitary $F$. In the source it identifies $D(ho_{CA}\|ho_C\otimesho_A)$ in the definition (2) of $H(C|A)$ with $D(ho_{AC}\|ho_A\otimesho_C)$ in (3), and likewise for $B$ in (4).
--
--   **Formalization Note** $D$ is the frozen `generalizedRelativeEntropy` of Frontier18.P01 (directed supremum over finite coordinate compressions of the finite-dimensional Lindblad relative entropy with trace correction and support condition), and $FXF^*$ is `swapCoeff X`, $(FXF^*)_{(j,i),(j',i')}=X_{(i,j),(i',j')}$. No positivity or trace-class hypothesis is needed: the identity holds for arbitrary arrays because the flip only permutes coordinates.
-- source:
--   Kuznetsova, Quantum conditional entropy for infinite-dimensional systems, arXiv:1004.4519v2, PDF p. 2, §1, identities (3)-(4) (H(C|A) via definition (2) on the swapped state); Lindblad, Commun. Math. Phys. 39 (1974), unitary invariance

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

theorem generalizedRelativeEntropy_swapCoeff {I J : Type} (X Y : Matrix (I × J) (I × J) ℂ) :
    generalizedRelativeEntropy (swapCoeff X) (swapCoeff Y) = generalizedRelativeEntropy X Y := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P18

end
