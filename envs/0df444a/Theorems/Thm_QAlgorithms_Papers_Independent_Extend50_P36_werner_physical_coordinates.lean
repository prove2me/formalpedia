-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P36_werner_physical_coordinates
-- name    : QAlgorithms.Papers.Independent.Extend50.P36.werner_physical_coordinates
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T14:12:21.273695+00:00
-- url     : https://prove2.me/theorems/cf3abc30-efc0-42f9-a6ed-3a4b689103fa
-- title:
--   Appendix A, reproduced background: full physical S3 Werner coordinates and positivity
-- statement:
--   All operators below act on $(\mathbb C^d)^{\otimes3}$ with $d\ge2$. Write $A=V_{AB}$, $B=V_{BC}$, $C=V_{CA}$, $T=V_{ABC}$ for the actual tensor-factor permutations, and $T^\dagger=V_{CBA}$. For either basis $B_+,B_-,B_0,B_1,B_2,B_3$, define real coordinates by $r_k=\operatorname{Tr}(wB_k)$. The allowed coordinates satisfy
--   $$r_++r_-+r_0=1,\quad r_+,r_-,r_0\ge0,\quad r_1^2+r_2^2+r_3^2\le r_0^2,$$
--   with $r_-=0$ at $d=2$.
--
--   For the Werner basis, set
--   $$R_\pm=(I\pm A\pm B\pm C+T+T^\dagger)/6,\quad R_0=(2I-T-T^\dagger)/3,$$
--   $$R_1=(2B-C-A)/3,\quad R_2=(A-C)/\sqrt3,\quad R_3=i(T-T^\dagger)/\sqrt3.$$
--   The collectively $U\otimes U\otimes U$ invariant density operators are exactly
--   $$w(r)=\frac{6r_+R_+}{d(d+1)(d+2)}+\frac{6r_-R_-}{d(d-1)(d-2)}+\frac3{2d(d^2-1)}\sum_{k=0}^3r_kR_k$$
--   for the allowed coordinates. At $d=2$ omit the $R_-$ summand. With the absent coordinate fixed to zero, the reconstruction is a density operator if and only if the displayed coordinate conditions hold; its extracted coordinates equal the supplied ones. Conversely every invariant density operator has that reconstruction and those coordinates.
--
--   This is a complete physical PSD parametrization.
-- source:
--   Compatible quantum correlations: on extension problems for Werner and isotropic states, arXiv:1305.1342v3, PDF p. 14, Appendix A, reproduced background: full physical S3 Werner coordinates and positivity

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P36

noncomputable section

open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Extend50.P36

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact accepted matrix alias; tensor reductions below compose frozen superoperators.

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

/-- Eqs.(A1)–(A4), PDF pp.14–15: complete physical Werner coordinate and PSD
characterization; at d=2 the absent antisymmetric sector has weight zero. -/
theorem werner_physical_coordinates (d : ℕ) (hd : 2 ≤ d) :
    CoordinateCharacterization false d := by sorry

end QAlgorithms.Papers.Independent.Extend50.P36

end
