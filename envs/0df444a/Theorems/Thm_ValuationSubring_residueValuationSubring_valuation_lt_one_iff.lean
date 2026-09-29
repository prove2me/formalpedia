-- Prove2me | Theorems.Thm_ValuationSubring_residueValuationSubring_valuation_lt_one_iff
-- name    : ValuationSubring.residueValuationSubring_valuation_lt_one_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.37934+00:00
-- url     : https://prove2.me/theorems/fe6b9866-880e-5cbf-8064-2b59643e8c3f
-- title:
--   Residue valuation detects the maximal ideal of A
-- statement:
--   Let $L$ be a field and let $A \le S$ be two valuation subrings of $L$, the inclusion being witnessed by $h$, and let $a \in A$. Here `A.residueValuationSubring S h` denotes the valuation subring of the residue field $\kappa(S) = S/\mathfrak m_S$ obtained as the image of the composite ring homomorphism $A \hookrightarrow S \to \kappa(S)$ (the inclusion $A \le S$ followed by the residue map); that this image is a valuation subring is the content of the definition, since for $x = \bar s \in \kappa(S)$ either $s \in A$, or $s$ is a unit of $S$ with $s^{-1} \in A$, giving $x^{-1}$ in the image, or $s$ is a non-unit of $S$ and $x = 0$. The theorem asserts the equivalence of two strict inequalities: the valuation attached to this subring of $\kappa(S)$, evaluated at the residue class in $\kappa(S)$ of the image of $a$ in $S$, is $< 1$ if and only if the valuation attached to $A$, evaluated at $a$ regarded as an element of $L$, is $< 1$.
--
--   This is the compatibility of a valuation with the valuation it induces on the residue field of a larger valuation ring: classically, the valuation of $A$ is the composite of the valuation of $S$ with that of $\bar A = A/\mathfrak m_S \subseteq \kappa(S)$, and $\mathfrak m_{\bar A} = \mathfrak m_A/\mathfrak m_S$. It is used in the study of regular prolongations of points on algebraic curves, where residue data must be transported between a valuation ring and its residue valuation ring.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_residueValuationSubring_valuation_lt_one_iff.lean

import Mathlib
import Definitions.Def_ValuationSubring_ResidueValuationSubring

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ValuationSubring.residueValuationSubring_valuation_lt_one_iff
    {L : Type*} [Field L] (A S : ValuationSubring L) (h : A ≤ S) (a : A) :
    (A.residueValuationSubring S h).valuation (IsLocalRing.residue S (A.inclusion S h a)) < 1 ↔
      A.valuation (a : L) < 1 := by sorry
