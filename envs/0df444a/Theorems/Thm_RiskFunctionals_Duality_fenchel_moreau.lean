-- Prove2me | Theorems.Thm_RiskFunctionals_Duality_fenchel_moreau
-- name    : RiskFunctionals.Duality.fenchel_moreau
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-22T03:50:59.971163+00:00
-- url     : https://prove2.me/theorems/6457c9be-7c3e-4fff-b376-57bb2fb2e8c9
-- title:
--   Theorem B.1 (Fenchel–Moreau–Rockafellar) — $h^{**}=h$ for proper l.s.c. convex $h$ on $L_p$
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a non-atomic probability space, $1\le p<\infty$, $\frac1p+\frac1q=1$, $\mathcal Y=L_p(\Omega,\mathcal F,P)$ and $\mathcal Z=L_q(\Omega,\mathcal F,P)$, paired by $\langle Y,Z\rangle=\mathbb E(YZ)$. Let $h:\mathcal Y\to[-\infty,+\infty]$ be proper ($h>-\infty$ everywhere and $h<+\infty$ somewhere), lower semicontinuous and convex (its epigraph $\{(Y,r):h(Y)\le r\}$ is convex). Then $h$ equals its biconjugate:
--   $$h(Y)=h^{**}(Y)=\sup_{Z\in\mathcal Z}\big\{\mathbb E(YZ)-h^*(Z)\big\},\qquad h^*(Z)=\sup_{Y\in\mathcal Y}\big\{\mathbb E(YZ)-h(Y)\big\}.$$
--
--   This is the basic duality theorem of convex analysis, on which every dual representation of §2.2.2 rests; its concave form ($g^{++}=g$ for proper u.s.c. concave $g$) gives representation (2.7).
--
--   **Formalization Note** The book states Theorem B.1 for general paired locally convex spaces; here it is instantiated on $(L_p,L_q)$, $1\le p<\infty$, the example of p. 269. Lower semicontinuity is for the norm topology of $L_p$ (equivalent to the weak one for convex $h$, p. 271). Only the second sentence of Theorem B.1 is stated here; the first is a separate item. The non-atomic hypothesis is the book's standing assumption (p. 4) and plays no role in this statement.
-- source:
--   Pflug & Römisch, Modeling, Measuring and Managing Risk, World Scientific 2007, p. 270, Theorem B.1 (second sentence)

import Mathlib
import Definitions.Def_RiskFunctionals_Duality_Functionals
import Definitions.Def_RiskFunctionals_Duality_Conjugates

namespace RiskFunctionals.Duality

open MeasureTheory ProbabilityTheory

/-- Theorem B.1 (Fenchel–Moreau–Rockafellar), second sentence (Pflug & Römisch, p. 270), on the
paired spaces `𝒴 = L_p`, `𝒵 = L_q`, `1 ≤ p < ∞`, `1/p + 1/q = 1`: if `h : 𝒴 → [−∞, +∞]` is
proper, l.s.c. and convex (convex epigraph), then `h** = h`. -/
theorem fenchel_moreau {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (hP : IsNonAtomic P) (p q : ENNReal) [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    [p.HolderConjugate q] (h : Lp ℝ p P → EReal) (hproper : IsProperConvex h)
    (hlsc : LowerSemicontinuous h) (hconv : ConvexEpi h) :
    convexBiconj q h = h := by sorry

end RiskFunctionals.Duality
