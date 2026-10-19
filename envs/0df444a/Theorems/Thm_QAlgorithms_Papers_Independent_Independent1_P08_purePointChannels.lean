-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P08_purePointChannels
-- name    : QAlgorithms.Papers.Independent.Independent1.P08.purePointChannels
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-18T19:17:08.922202+00:00
-- url     : https://prove2.me/theorems/c4553f95-4a8a-436f-908c-5e35d89461d5
-- title:
--   Pure point channels are extreme
-- statement:
--   Let $t\in\mathbb R^3$ with $\|t\|_2\le1$, and set $R=(I+t\cdot\sigma)/2$. The canonical point map is CPT and CQ, $R$ is a density matrix, and on every operator $X$ it satisfies
--
--   $$\Phi_{t,0}(X)=\operatorname{Tr}(X)R.$$
--
--   If $\|t\|_2=1$, there is a unit vector $\psi$ with $R=|\psi\rangle\langle\psi|$, and the map is extreme in both the CPT and EBT sets. This identifies the pure-output endpoint of the point-channel family.
-- source:
--   Qubit Entanglement Breaking Channels, arXiv:quant-ph/0302032v3, Pure point channels are extreme, PDF p. 11. https://arxiv.org/abs/quant-ph/0302032v3 . PDF SHA-256: dba60bd30b3ca1e23dac55f1e413d595e822e7d75c0dff71bf1b94f65337b81d.

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










































































/-- Point channels, PDF p.11: purity and extremality from unit Bloch length. -/
theorem purePointChannels (t : Bloch) (ht : blochNorm t ≤ 1) :
    CPT (canonical t 0) ∧ IsCQMap (canonical t 0) ∧ IsDensityMatrix (blochDensity t) ∧
    (∀ X, canonical t 0 X = X.trace • blochDensity t) ∧
    (blochNorm t = 1 →
      (∃ psi : EuclideanSpace ℂ Bool, IsState psi ∧ blochDensity t = pureDensity psi) ∧
      canonical t 0 ∈ cptSet.extremePoints ℝ ∧ canonical t 0 ∈ ebtSet.extremePoints ℝ) := by sorry











end QAlgorithms.Papers.Independent.Independent1.P08
