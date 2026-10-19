-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P08_planarSameBasis
-- name    : QAlgorithms.Papers.Independent.Independent1.P08.planarSameBasis
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T19:17:30.72834+00:00
-- url     : https://prove2.me/theorems/82861cca-76e2-41e9-8933-6d2baffcdf70
-- title:
--   Remark a planar same-basis convex decomposition
-- statement:
--   Suppose $\Phi_{t,\lambda}$ is EBT and $\lambda_j=0$ for a chosen coordinate $j$. It belongs to the real convex hull of canonical CQ maps $\Phi_{t',\lambda'}$ satisfying $\lambda'_j=0$ and having at most one nonzero coordinate of $\lambda'$. Moreover, if $\Xi_{t_3,0}$ denotes the CPT parameter slice fixing only $t_3$ and $\lambda_3=0$, then
--
--   $$\Xi_{t_3,0}=\operatorname{conv}_{\mathbb R}\{(t,\lambda)\in\Xi_{t_3,0}:\Phi_{t,\lambda}\text{ is CQ}\}.$$
--
--   This preserves the canonical coordinate plane, including point-channel endpoints; the other translation coordinates may vary.
-- source:
--   Qubit Entanglement Breaking Channels, arXiv:quant-ph/0302032v3, Remark a planar same-basis convex decomposition, PDF p. 16. https://arxiv.org/abs/quant-ph/0302032v3 . PDF SHA-256: dba60bd30b3ca1e23dac55f1e413d595e822e7d75c0dff71bf1b94f65337b81d.

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

















































































/-- Remark (a), PDF p.16: same-basis planar decomposition and fixed-t3 slice. -/
theorem planarSameBasis :
    (∀ t lam : Bloch, EBT (canonical t lam) → ∀ j, lam j = 0 →
      canonical t lam ∈ convexHull ℝ (planarCQ j)) ∧
    ∀ t3 : ℝ, zeroThirdSlice t3 = convexHull ℝ
      {p : Bloch × Bloch | p ∈ zeroThirdSlice t3 ∧ IsCQMap (canonical p.1 p.2)} := by sorry




end QAlgorithms.Papers.Independent.Independent1.P08
