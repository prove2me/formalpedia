-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P22_sharp_rotor_code
-- name    : QAlgorithms.Papers.Independent.Extend50.P22.sharp_rotor_code
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T17:27:07.932918+00:00
-- url     : https://prove2.me/theorems/e752aa5a-da0b-4acb-bee6-76eece400065
-- title:
--   Unnumbered sharp-cutoff three-rotor code, Eqs.(36)–(38), (D.9)
-- statement:
--   Let $h,m$ be nonnegative integers with $h\le m$. The normalized isometry $V|x\rangle=(2m+1)^{-1/2}\sum_{y=-m}^m|-3y,y-x,2(x+y)\rangle$, $-h\le x\le h$, is embedded in finite coordinate intervals containing its entire support. For uniform located single erasure, let $e$ be the optimal worst-case entanglement error. Then $$e\le\sqrt{\frac{4h}{2m+1}},\qquad 2h\le6\max\{6m,2(m+h),4(m+h)\}\,e.$$ Thus the source’s upper asymptotic estimate has leading form $\sqrt{2h/m}$ when $m$ grows. The exact expression includes $h=m=0$ without division by zero. For the explicit diagonal charges TL|x>=x|x> and Ti|a>=a|a> in these centered interval coordinates, the code also satisfies (sum_i Ti)V=V TL; this is the source’s natural U(1) covariance, now an explicit conclusion.
-- source:
--   Continuous symmetries and approximate quantum error correction, arXiv:1902.07714v1, PDF p. 11, Unnumbered sharp-cutoff three-rotor code, Eqs.(36)–(38), (D.9)

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P22

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Extend50.P22

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P22 (bell)

open QAlgorithms.Papers.Independent.Support21.P09 (Irreducible)

open QAlgorithms.Papers.Independent.Renew46.P45 (symmetricWeight)

/-- PDF pp.11,41, (36)–(38),(D.9): the fixed sharp code conserves the natural
integer total charge and has the stated recovery bounds.
SOURCE CORRECTION: p.11 says every physical dimension is 2m+1; (36) and
(D.11) instead require charge intervals [-3m,3m], [-m-h,m+h], and
[-2(m+h),2(m+h)]. We use these explicit interval embeddings without deleting
amplitudes. D.2 prints min_i, whereas D.8–D.9 use the common upper bound
sqrt(4h/(2m+1)); the latter is retained. The m=h=0 singleton is included. -/
theorem sharp_rotor_code (h m : ℕ) (hm : h ≤ m) :
    let TL : Matrix (Fin (2 * h + 1)) (Fin (2 * h + 1)) ℂ :=
      Matrix.diagonal (fun x => (x.val : ℂ) - (h : ℂ))
    let Ti : (i : Fin 3) → Matrix (Fin (sharpDims h m i)) (Fin (sharpDims h m i)) ℂ :=
      fun i => Matrix.diagonal (fun y => (y.val : ℂ) -
        ((![3 * m, m + h, 2 * (m + h)] i : ℕ) : ℂ))
    (∑ i : Fin 3, liftLocal i (Ti i)) * sharpEncoding h m = sharpEncoding h m * TL ∧
    ∃ c : CovariantErasureCodeData (2 * h + 1) 3, c.dims = sharpDims h m ∧ HEq c.V (sharpEncoding h m) ∧
      errorWorst c.uniformNoise ≤ Real.sqrt (4 * (h : ℝ) / (2 * m + 1)) ∧
      (2 * (h : ℝ)) ≤
        6 * max (6 * (m : ℝ)) (max (2 * (m + h : ℝ)) (4 * (m + h : ℝ))) *
          errorWorst c.uniformNoise := by sorry

end QAlgorithms.Papers.Independent.Extend50.P22

end
