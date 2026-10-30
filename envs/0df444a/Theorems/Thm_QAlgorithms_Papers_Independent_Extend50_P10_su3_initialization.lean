-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P10_su3_initialization
-- name    : QAlgorithms.Papers.Independent.Extend50.P10.su3_initialization
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T19:45:16.789932+00:00
-- url     : https://prove2.me/theorems/91e6f597-78be-47f2-af42-2bf9295d88e6
-- title:
--   Corrected three-row initialization with determinant singlets
-- statement:
--   Let $a,b,c\ge0$ and $n=a+2b+3c\ge1$. In a qutrit alphabet $u,d,s$, put $|p\rangle=(|ud\rangle-|du\rangle)/\sqrt2$ and
--
--   $$
--   |q\rangle=\frac{|uds\rangle-|usd\rangle+|dsu\rangle-|dus\rangle+|sud\rangle-|sdu\rangle}{\sqrt6}.
--   $$
--
--   Then $|\Psi\rangle=|u\rangle^{\otimes a}\otimes|p\rangle^{\otimes b}\otimes|q\rangle^{\otimes c}$ satisfies
--
--   $$
--   \|\Psi\|=1,\qquad P_{(a+b+c,b+c,c)}|\Psi\rangle=|\Psi\rangle.
--   $$
--
--   Here $P_\lambda$ is the full physical $\lambda$-isotypic projector. **Source correction:** the printed rows $(n_0+k+c,n_0-k+c,c)$ must be $((n_0+k)/2+c,(n_0-k)/2+c,c)$ for $n_0=a+2b$ and $k=a$; the printed shape has too many boxes. Pair normalization is inherited from Eq.(5). Independent moderation of this correction is pending.
-- source:
--   Speeding up Learning Quantum States through Group Equivariant Convolutional Quantum Ansätze, arXiv:2112.07611v3, PDF p. 10, Unnumbered §IV.B: three-row initialization by antisymmetric pairs and singlets

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P10

noncomputable section

open scoped Matrix

open QAlgorithms

open QAlgorithms.Schur

open QAlgorithms.Papers.Independent.Information100.P44 (matrixUnit)

namespace QAlgorithms.Papers.Independent.Extend50.P10

attribute [local instance] Classical.propDecidable

/-- PDF p.10, §IV.B, corrected three-row initialization. The printed rows
(n+k+l,n−k+l,l) are replaced by ((n+k)/2+l,(n−k)/2+l,l), as forced by
physical site count. This source correction requires independent moderation. -/
theorem su3_initialization (a b c : ℕ) (_hn : 1 ≤ a+2*b+3*c) :
    ‖su3Initialization a b c‖ = 1 ∧
    act (physicalShapeProjector 3 (a+2*b+3*c) (threeRowDiagram a b c))
      (su3Initialization a b c) = su3Initialization a b c := by sorry

end QAlgorithms.Papers.Independent.Extend50.P10

end
