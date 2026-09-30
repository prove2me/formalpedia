-- Prove2me | Theorems.Thm_StarShapedRisk_LawInvariant_fsd_consistent
-- name    : StarShapedRisk.LawInvariant.fsd_consistent
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T23:11:09.035831+00:00
-- url     : https://prove2.me/theorems/58e91a63-d528-4548-9c3a-5c109c053074
-- title:
--   Proof of Theorem 5 — monotone law-invariant risk functionals respect first-order dominance
-- statement:
--   Let $P$ be an atomless probability measure on $(\Omega,\mathcal F)$, let $\mathcal X$ be the space of bounded measurable losses with the pointwise order, and let $\rho:\mathcal X\to\mathbb R$ be monotone ($X\geqq Y\Rightarrow\rho(X)\ge\rho(Y)$) and law-invariant under $P$. Then for all $X,Y\in\mathcal X$,
--   $$X\succsim_{\mathrm{FSD}}Y\ \Longrightarrow\ \rho(X)\le\rho(Y),$$
--   where $X\succsim_{\mathrm{FSD}}Y$ means $P(X\le x)\ge P(Y\le x)$ for every real $x$.
--
--   Consistency with first-order dominance is what lets the proof of Theorem 5 replace the acceptance set $\mathcal A_\rho$ by the union of the FSD-lower sets of its elements. Atomlessness is essential: on a space with atoms, two laws ordered by FSD need not be realized by pointwise ordered positions.
--
--   **Formalization Note** Only monotonicity and law invariance are assumed; translation invariance and normalization are not needed and are not included. Measurability of the positions is part of the space $\mathcal X$.
-- source:
--   Castagnoli, Cattelan, Maccheroni, Tebaldi, Wang, Star-Shaped Risk Measures, Operations Research 70(5) (2022), p. 2652, Appendix, proof of Theorem 5, display after Eq. (A.1)

import Mathlib
import Definitions.Def_StarShapedRisk_LawInvariant_Model
import Definitions.Def_StarShapedRisk_LawInvariant_VaR

namespace StarShapedRisk.LawInvariant

open MeasureTheory

/-- Castagnoli et al. (2022), proof of Theorem 5, the display after (A.1) (p. 2652): on an
atomless probability space, a monotone and law-invariant `ρ` is consistent with first-order
stochastic dominance: `X ≿FSD Y ⇒ ρ X ≤ ρ Y`. -/
theorem fsd_consistent {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (hP : IsAtomless P)
    (ρ : Positions Ω → ℝ) (hmono : IsMonotone ρ) (hlaw : IsLawInvariant P ρ)
    (X Y : Positions Ω) (hXY : FSD P X.1 Y.1) :
    ρ X ≤ ρ Y := by sorry

end StarShapedRisk.LawInvariant
