-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P08_linearChannels
-- name    : QAlgorithms.Papers.Independent.Independent1.P08.linearChannels
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-18T19:16:22.125283+00:00
-- url     : https://prove2.me/theorems/78ff9453-0fac-4a6c-9022-84ef2db730cc
-- title:
--   Linear channels and equation 9
-- statement:
--   For $t\in\mathbb R^3$ and $a\in\mathbb R$, let $\Phi=\Phi_{t,(0,0,a)}$. Then
--
--   $$\Phi\text{ is CPT}\iff t_1^2+t_2^2+(|t_3|+|a|)^2\le1.$$
--
--   Whenever this holds, $\Phi$ is CQ and equals $X\mapsto\sum_{b=0}^1\operatorname{Tr}(|b\rangle\langle b|X)R_b$, where $R_0=(I+(t+ae_3)\cdot\sigma)/2$ and $R_1=(I+(t-ae_3)\cdot\sigma)/2$. This includes $a=0$, when the image is a point.
-- source:
--   Qubit Entanglement Breaking Channels, arXiv:quant-ph/0302032v3, Linear channels and equation 9, PDF p. 6. https://arxiv.org/abs/quant-ph/0302032v3 . PDF SHA-256: dba60bd30b3ca1e23dac55f1e413d595e822e7d75c0dff71bf1b94f65337b81d.

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





































































/-- Linear channels, PDF pp.6,12, (8)-(9), with explicit output Bloch vectors. -/
theorem linearChannels (t : Bloch) (a : ℝ) :
    (CPT (canonical t ![0,0,a]) ↔ t 0^2+t 1^2+(|t 2|+|a|)^2 ≤ 1) ∧
    (CPT (canonical t ![0,0,a]) → IsCQMap (canonical t ![0,0,a]) ∧
      canonical t ![0,0,a] = holevoMap
        (fun b : Bool => blochDensity (t + Pi.single 2 (if b then -a else a)))
        (fun b : Bool => pureDensity (ket b))) := by sorry
















end QAlgorithms.Papers.Independent.Independent1.P08
