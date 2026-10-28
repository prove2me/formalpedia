-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier30_P20_lemma22
-- name    : QAlgorithms.Papers.Independent.Frontier30.P20.lemma22
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T18:50:06.422906+00:00
-- url     : https://prove2.me/theorems/a5535ad6-7cce-4b72-8583-f4fcf3fdbfed
-- title:
--   Lemma 22 (uniqueness of class-3 channel)
-- statement:
--   Let $T$ be a CPTP map on $M_2(\mathbb C)$, a qubit channel. Composition applies the rightmost factor first; map norms are induced Hilbert–Schmidt norms. Fix $x,c_1\in(0,1)$ and $\phi\in[0,2\pi)$. Set $c_0=\sqrt{1-c_1^2}$,
--
--   $$|c\rangle=c_0e^{i\phi}|0\rangle+c_1|1\rangle,\qquad |c^{\prime}\rangle=\sqrt{1-x^2c_1^2}e^{i\phi}|0\rangle+xc_1|1\rangle.$$
--
--   There exists exactly one canonical class-3 channel $C$ satisfying $C(|c\rangle\langle c|)=|c^{\prime}\rangle\langle c^{\prime}|$. Class 3 means the Eq.(37) canonical representation outside classes 1 and 2, with the nondegenerate parameters of the paragraph following the lemma.
--
--   The uniqueness concerns the channel, not its Kraus vectors.
-- source:
--   Dividing Quantum Channels, arXiv:math-ph/0611057v3, PDF p. 19, Lemma 22 (uniqueness of class-3 channel)

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P20

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator Topology

namespace QAlgorithms.Papers.Independent.Frontier30.P20

open QAlgorithms.Papers.Independent.Information100.P26 (Mat outer)

open QAlgorithms.Papers.Independent.Dependency50.P14 (Super)

-- Accepted matrix-unit coordinates on the action of a superoperator.

local notation "coefficients" =>
  QAlgorithms.Papers.Independent.Dependency50.P12.superOfAction

/-- Lemma 22, PDF pp.18--19: uniqueness of the channel on the nondegenerate class-3 parameter domain. -/
theorem lemma22 (c1 x phi : ℝ) (hc0 : 0 < c1) (hc1 : c1 < 1)
    (hx0 : 0 < x) (hx1 : x < 1) (hphi0 : 0 ≤ phi) (hphi1 : phi < 2 * Real.pi) :
    ∃! T : Super 2, ClassThree T ∧
      T (outer (classInput c1 phi) (classInput c1 phi)) =
        outer (classOutput c1 x phi) (classOutput c1 x phi) := by sorry

end QAlgorithms.Papers.Independent.Frontier30.P20

end
