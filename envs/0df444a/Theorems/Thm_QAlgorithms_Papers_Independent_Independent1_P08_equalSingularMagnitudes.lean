-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P08_equalSingularMagnitudes
-- name    : QAlgorithms.Papers.Independent.Independent1.P08.equalSingularMagnitudes
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T19:18:01.303657+00:00
-- url     : https://prove2.me/theorems/f643e568-d373-4c1d-9731-7babc3e65c42
-- title:
--   Remark d equal singular magnitudes
-- statement:
--   Let $\Phi=\Phi_{t,\lambda}$ be EBT, with $|\lambda_j|=a>0$ for all three coordinates. There are input/output unitaries $U,V$ and $s\in\{a,-a\}$ such that, writing $\mathcal B(\Psi)=\operatorname{Ad}_V\circ\Psi\circ\operatorname{Ad}_U$,
--
--   $$\mathcal B(\Phi)=\Phi_{(\|t\|_2,0,0),(s,s,s)}\in\operatorname{conv}_{\mathbb R}(\mathcal A).$$
--
--   Here $\mathcal A$ consists of canonical CQ maps for which $t_j=\lambda_j=0$ for some $j\in\{2,3\}$. Also $\Phi\in\operatorname{conv}_{\mathbb R}(\mathcal B^{-1}(\mathcal A))$. Thus summands are canonical in the rotated basis and need not be canonical in the original one.
-- source:
--   Qubit Entanglement Breaking Channels, arXiv:quant-ph/0302032v3, Remark d equal singular magnitudes, PDF p. 17. https://arxiv.org/abs/quant-ph/0302032v3 . PDF SHA-256: dba60bd30b3ca1e23dac55f1e413d595e822e7d75c0dff71bf1b94f65337b81d.

import Definitions.Def_QAlgorithms_Defs_QubitBlochMaps
import Definitions.Def_QAlgorithms_Defs_FiniteRegisters
import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P08_Model
set_option autoImplicit false

/-! Ruskai, Qubit Entanglement Breaking Channels, arXiv:quant-ph/0302032v3.
All locators are PDF pages. Convexity is real; ambiguous claims are in HARD.md. -/

noncomputable section

open scoped Matrix ComplexOrder

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Independent1.P08

open QAlgorithms.Entanglement QAlgorithms.QubitChannels




















































































/-- Remark (d), PDF p.17: align signed singular magnitudes and translation in rotated bases. -/
theorem equalSingularMagnitudes (t lam : Bloch) (a : ℝ) (ha : 0 < a)
    (habs : ∀ j, |lam j| = a) (hPhi : EBT (canonical t lam)) :
    ∃ U V : Matrix.unitaryGroup Bool ℂ, ∃ s : ℝ, (s = a ∨ s = -a) ∧
      changeBases U V (canonical t lam) = canonical ![blochNorm t,0,0] (fun _ => s) ∧
      changeBases U V (canonical t lam) ∈ convexHull ℝ axialCQ ∧
      canonical t lam ∈ convexHull ℝ {Psi | ∃ C ∈ axialCQ, changeBases U V Psi = C} := by sorry

end QAlgorithms.Papers.Independent.Independent1.P08
