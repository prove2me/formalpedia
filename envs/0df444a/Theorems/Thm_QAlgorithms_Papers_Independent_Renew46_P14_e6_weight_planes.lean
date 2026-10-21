-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P14_e6_weight_planes
-- name    : QAlgorithms.Papers.Independent.Renew46.P14.e6_weight_planes
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T20:15:51.933924+00:00
-- url     : https://prove2.me/theorems/a998db06-6126-49ba-b22a-5360e52d8647
-- title:
--   E6: the corrected nine-root tensor weight array
-- statement:
--   Work in $\mathbb R^8$ with the paper's fixed orthonormal basis $k_1,\ldots,k_8$. Let $R_L$ denote the coordinate roots of the complex Lie algebra $L$ in Table 2. Let $\Pi=\operatorname{span}_{\mathbb R}(k_1-k_2,k_2-k_3)$, let $p$ be its orthogonal projection, let $A=\{k_i-k_j:1\le i\ne j\le3\}$, and put $w_c=(k_1+k_2+k_3-3k_c)/3$. Let $\rho_c$ cyclically permute the first three axes to send $k_1$ to $k_c$, fixing the other axes. A minus sign on a root set negates each whole vector.
--
--   Let
--   $$b_1=\frac{k_4+k_5}{\sqrt2},\quad b_2=\frac{z-\sqrt3k_6}{\sqrt6},\quad c_1=\frac{k_4-k_5}{\sqrt2},\quad c_2=\frac{z+\sqrt3k_6}{\sqrt6},\qquad z=k_1+k_2+k_3.$$
--   These four vectors are orthonormal. The offsets are
--   $$\begin{aligned}
--   u_1&=(-5k_1+k_2+k_3+3k_4-3k_5-\sqrt3k_6)/6, &v_1&=(-5k_1+k_2+k_3+3k_4+3k_5+\sqrt3k_6)/6,\\
--   u_2&=(-k_1+2k_2+2k_3+\sqrt3k_6)/3,&v_2&=(-k_1+2k_2+2k_3-\sqrt3k_6)/3,\\
--   u_3&=(-5k_1+k_2+k_3-3k_4+3k_5-\sqrt3k_6)/6,&v_3&=(-5k_1+k_2+k_3-3k_4-3k_5+\sqrt3k_6)/6.
--   \end{aligned}$$
--   Each $u_i$ is orthogonal to $b_1,b_2$, and each $v_i$ to $c_1,c_2$. Put $\lambda_1=(\sqrt2/2,-\sqrt6/6)$, $\lambda_2=(0,\sqrt6/3)$, and $\lambda_3=(-\sqrt2/2,-\sqrt6/6)$. There is a unique intersection root $r_{ij}$ for each $i,j\in\{1,2,3\}$, given by
--   $$r_{ij}=u_i+\lambda_{j,1}b_1+\lambda_{j,2}b_2=v_j+\lambda_{i,1}c_1+\lambda_{i,2}c_2.$$
--   Precisely, $(u_i+\operatorname{span}(b_1,b_2))\cap(v_j+\operatorname{span}(c_1,c_2))=\{r_{ij}\}$. These nine distinct roots exhaust the highest-weight block (4.4). Their explicit array is
--   $$\begin{pmatrix}
--   -k_1+k_4 & \frac{-k_1+k_2+k_3+k_4-k_5-\sqrt3k_6}{2} & -k_1-k_5\\
--   \frac{-k_1+k_2+k_3+k_4+k_5+\sqrt3k_6}{2} & k_2+k_3 & \frac{-k_1+k_2+k_3-k_4-k_5+\sqrt3k_6}{2}\\
--   -k_1+k_5 & \frac{-k_1+k_2+k_3-k_4+k_5-\sqrt3k_6}{2} & -k_1-k_4
--   \end{pmatrix}.$$
--   Negating the offsets and weights gives the opposite root and the corresponding singleton intersection.
--
--   This is the distinguished-root $(3,3)$ weight array. The positive-plane headings and entry $(3,2)$ correct the two printing errors fixed by the page-12 offsets.
-- source:
--   Exceptional Lie Algebras, SU(3) and Jordan Pairs, arXiv:1112.1258v2, PDF p. 12, §4.2.3, Table 3: the (3 tensor 3) weight array and orthogonal planes

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P14

namespace QAlgorithms.Papers.Independent.Renew46.P14

noncomputable section

open scoped BigOperators

local instance : DecidableEq V := Classical.decEq V

attribute [local instance] Classical.propDecidable

/-- The corrected Table 3 array: unique intersections, coordinates, and opposite signs.
Source: §4.2.3, PDF pp. 12–13. Corrections are documented in `tableRoot`. -/
theorem e6_weight_planes :
    (∀ i j : Fin 4, dotProduct (planeFrame i) (planeFrame j) = if i = j then 1 else 0) ∧
    (∀ i : Fin 3, dotProduct (firstPlaneOffsets i) (planeFrame 0) = 0 ∧ dotProduct (firstPlaneOffsets i) (planeFrame 1) = 0 ∧
      dotProduct (secondPlaneOffsets i) (planeFrame 2) = 0 ∧ dotProduct (secondPlaneOffsets i) (planeFrame 3) = 0) ∧
    Function.Injective (fun ij : Fin 3 × Fin 3 => tableRoot ij.1 ij.2) ∧
    Finset.univ.image (fun ij : Fin 3 × Fin 3 => tableRoot ij.1 ij.2) = block2 ∧
    (∀ i j : Fin 3,
      tableRoot i j = firstPlaneOffsets i + (tableWeights j).1 • planeFrame 0 + (tableWeights j).2 • planeFrame 1 ∧
      tableRoot i j = secondPlaneOffsets j + (tableWeights i).1 • planeFrame 2 + (tableWeights i).2 • planeFrame 3 ∧
      plane (firstPlaneOffsets i) (planeFrame 0) (planeFrame 1) ∩
        plane (secondPlaneOffsets j) (planeFrame 2) (planeFrame 3) = {tableRoot i j} ∧
      -tableRoot i j = -firstPlaneOffsets i + (-(tableWeights j).1) • planeFrame 0 +
        (-(tableWeights j).2) • planeFrame 1 ∧
      -tableRoot i j = -secondPlaneOffsets j + (-(tableWeights i).1) • planeFrame 2 +
        (-(tableWeights i).2) • planeFrame 3 ∧
      plane (-firstPlaneOffsets i) (planeFrame 0) (planeFrame 1) ∩
        plane (-secondPlaneOffsets j) (planeFrame 2) (planeFrame 3) = {-tableRoot i j}) := by sorry

end

end QAlgorithms.Papers.Independent.Renew46.P14
