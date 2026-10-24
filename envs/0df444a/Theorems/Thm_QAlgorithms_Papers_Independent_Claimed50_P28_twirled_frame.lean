-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P28_twirled_frame
-- name    : QAlgorithms.Papers.Independent.Claimed50.P28.twirled_frame
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T12:17:54.785216+00:00
-- url     : https://prove2.me/theorems/318f8957-ac4b-4a83-9aca-a6774b2e9446
-- title:
--   Four-sector twirled frame and inverse trace
-- statement:
--   Let $d\ge2$ and let the positive nonzero seeds $\Pi_j$ satisfy $\sum_j\operatorname{Tr}\Pi_j=d$. The covariant frame is $F=\sum_j\int d|\Pi_{j,U,V}\rangle\!\rangle\langle\!\langle\Pi_{j,U,V}|/\operatorname{Tr}\Pi_j$, with two independent normalized Haar measures. Set $m=d^2-1$, $\Omega=|I\rangle\!\rangle\langle\!\langle I|/d$, and let $P_1=\Omega_{13}\otimes\Omega_{24}$, $P_2=(I-\Omega)_{13}\otimes\Omega_{24}$, $P_3=\Omega_{13}\otimes(I-\Omega)_{24}$ and $P_4=(I-\Omega)_{13}\otimes(I-\Omega)_{24}$. Wires are permuted from natural vectorization order to the pairs $13,24$. Define
--
--   $$A=\frac{\sum_j\operatorname{Tr}[(\operatorname{Tr}_{\rm in}\Pi_j)^2]/\operatorname{Tr}\Pi_j-1}{m},\quad B=\frac{\sum_j\operatorname{Tr}[(\operatorname{Tr}_{\rm out}\Pi_j)^2]/\operatorname{Tr}\Pi_j-1}{m},$$
--   $$C=\frac{\sum_j d\operatorname{Tr}(\Pi_j^2)/\operatorname{Tr}\Pi_j-m(A+B)-1}{m^2}.$$
--
--   Then $F=P_1+AP_2+BP_3+CP_4$. The sector dimensions are $1,m,m,m^2$. If $A,B,C>0$, its inverse equals its support inverse and
--
--   $$\operatorname{Tr}F^{-1}=1+m\left(\frac1A+\frac1B+\frac mC\right).$$
--
--   This formula does not assign a finite full-tomography loss to an unmeasured sector.
-- source:
--   Optimal quantum tomography for states, measurements, and transformations, arXiv:0806.1172v1, PDF p. 3, (27)–(30); note [12]

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P28

noncomputable section

open MeasureTheory

open scoped BigOperators ComplexConjugate ComplexOrder Matrix Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Claimed50.P28

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact accepted aliases/pairing; unrelated short-name collisions are not reused.

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Frontier18.P17 (hs)

/-- PDF p.3, (27)–(30), and p.4 note [12]: the four-sector frame, dimensions,
and full-inverse trace. The full inverse clause requires strictly positive A,B,C. -/
theorem twirled_frame {d : ℕ} (hd : 2 ≤ d) {J : Type*} [Fintype J]
    (haar : Measure (SU d)) (hhaar : IsProbabilityHaar haar)
    (P : J → Op (ChoiBasis d)) (hP : Seeds P) :
    let A := coefficientA P
    let B := coefficientB P
    let C := coefficientC P
    let F := twirledFrame haar P
    F = sector d 0 + (A : ℂ) • sector d 1 + (B : ℂ) • sector d 2 + (C : ℂ) • sector d 3 ∧
    (sector d 0).trace.re = 1 ∧
    (sector d 1).trace.re = (d : ℝ)^2 - 1 ∧
    (sector d 2).trace.re = (d : ℝ)^2 - 1 ∧
    (sector d 3).trace.re = ((d : ℝ)^2 - 1)^2 ∧
    (0 < A → 0 < B → 0 < C →
      F⁻¹ = frameSupportInverse F ∧
      (F⁻¹).trace.re = 1 + ((d : ℝ)^2 - 1) *
        (1/A + 1/B + ((d : ℝ)^2 - 1)/C)) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P28

end
