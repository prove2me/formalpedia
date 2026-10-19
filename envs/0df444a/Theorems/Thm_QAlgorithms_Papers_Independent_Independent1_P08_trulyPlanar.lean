-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P08_trulyPlanar
-- name    : QAlgorithms.Papers.Independent.Independent1.P08.trulyPlanar
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-18T19:17:09.118041+00:00
-- url     : https://prove2.me/theorems/9269405d-7658-4d15-a1bd-d8ca2de99d5f
-- title:
--   Truly planar channels do not touch the Bloch sphere
-- statement:
--   Let $\Phi_{t,\lambda}$ be a CPT canonical qubit map. If exactly one coordinate of $\lambda$ is zero, then
--
--   $$\|t+\operatorname{diag}(\lambda)v\|_2<1\qquad(\|v\|_2\le1).$$
--
--   Also, when $\lambda_3=0$, $(|\lambda_1|+|\lambda_2|)^2+\|t\|_2^2\le1$. If both $\lambda_1,\lambda_2$ are nonzero and equality holds, then $t_1=t_2=0$. Thus a truly planar image stays strictly inside the Bloch sphere.
-- source:
--   Qubit Entanglement Breaking Channels, arXiv:quant-ph/0302032v3, Truly planar channels do not touch the Bloch sphere, PDF p. 12. https://arxiv.org/abs/quant-ph/0302032v3 . PDF SHA-256: dba60bd30b3ca1e23dac55f1e413d595e822e7d75c0dff71bf1b94f65337b81d.

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











































































/-- Truly planar images, PDF p.12, including (23). The repeated t2-square is a
typographical expansion; the standing Euclidean meaning of |t| is retained. -/
theorem trulyPlanar (t lam : Bloch) (hPhi : CPT (canonical t lam)) :
    ((Finset.univ.filter fun j => lam j = 0).card = 1 →
      ∀ v : Bloch, blochNorm v ≤ 1 → blochNorm (t + fun j => lam j*v j) < 1) ∧
    (lam 2 = 0 → (|lam 0|+|lam 1|)^2+blochNorm t^2 ≤ 1) ∧
    (lam 2 = 0 → lam 0 ≠ 0 → lam 1 ≠ 0 →
      (|lam 0|+|lam 1|)^2+blochNorm t^2 = 1 → t 0 = 0 ∧ t 1 = 0) := by sorry










end QAlgorithms.Papers.Independent.Independent1.P08
