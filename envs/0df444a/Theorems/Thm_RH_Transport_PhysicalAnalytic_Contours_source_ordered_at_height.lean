-- Prove2me | Theorems.Thm_RH_Transport_PhysicalAnalytic_Contours_source_ordered_at_height
-- name    : RH.Transport.PhysicalAnalytic.Contours.source_ordered_at_height
-- status  : Proved
-- author  : @Himan
-- created : 2026-11-15T20:03:36.580895+00:00
-- url     : https://prove2.me/theorems/84051466-1976-4211-9250-f7bc6c4f7e56
-- title:
--   Moving the $w$-contour of the source integral from $\operatorname{Re}w=c_w$ to $\tfrac{19}{20}$ at a fixed point $s$ right of the transported boundary
-- statement:
--   Throughout, $\mathcal O=\mathbb Z[\zeta_3]$, a *Hecke character* is a finite-order Hecke character of $\mathbb Q(\zeta_3)$ in OpenAI's family-003 development, and $\beta$ is the supremum of the real parts of the zeros of the associated Hecke $L$-functions (pole exception excluded, sentinel at $1/2$). Objects named in typewriter font are those of OpenAI's development. The *tuned* constants are those of LW56e2's refinement, from the definition bundle `Transport_TunedCandidate`:
--   $$
--   p=\tfrac{214651}{1250000000},\qquad b=\tfrac{192821}{1562500},\qquad \ell=\tfrac16+p,\qquad l_x=\tfrac{1-\ell-b}2,\qquad l_y=\tfrac{1-\ell+b}2,\qquad h=\tfrac{1+3\ell+b}2,\qquad\zeta_0=\tfrac1{8\cdot10^{12}},
--   $$
--   the tuned boundary $B=\tfrac{11}{12}-\tfrac\ell4=\tfrac78-\tfrac p4$, also written $B_p$, and the signal exponent $\operatorname{sig}(s)=s+\tfrac{l_x}2-1+\tfrac h6=s-\tfrac23-\tfrac b6$. OpenAI's development has $\ell=\tfrac16$ and $b=\tfrac18$, hence $l_x=\tfrac{17}{48}$, $l_y=\tfrac{23}{48}$, boundary $\tfrac78$ and $\operatorname{sig}(s)=s-\tfrac{11}{16}$.
--
--   **Setting.** Let $\eta$ be a Hecke character, $S$ a finite set of ideals with the source exclusions, $J$ a finite set of slots with slot sets $T_j$ of prime ideals outside $S$ and slot coefficients $b_j$, and $W_0,W_1^\ast$ Schwartz functions supported in $[a_0,b_0]$ and $[a_1,b_1]$ with $a_0,a_1>0$. Let $X,Y,Z>0$, let $a,t$ be real with
--   $$
--   B_p\le a,\qquad \beta<a,\qquad a+it\ne1,
--   $$
--   and let $c_w>1$, $e>0$. Put $s=a+it$, let $\pi$ be the fixed source principal character of $S$, and
--   $$
--   K(w,z)=\texttt{sourceMultiplier}\big(W_0,W_1^\ast,X,Y,Z;\eta_S;s;\ \texttt{globalClosedCorrection}(\eta,S,s),\ \texttt{slotMultiplier}(\eta,J,T,b,s)\big)(w,z),
--   $$
--   where $\eta_S$ is $\eta$ with the primes of $S$ excluded.
--
--   **Statement.** Writing $\int_{(c)}$ for `verticalIntegral c`,
--   $$
--   \int_{(\frac16+e)}\!\int_{(c_w)}K(w,z)\,L(\pi,6z)\,L(\pi,w)\,dw\,dz=\int_{(\frac16+e)}\!\int_{(\frac{19}{20})}K(w,z)\,L(\pi,6z)\,L(\pi,w)\,dw\,dz+R_\pi\int_{(\frac{33}{200})}K(1,z)\,L(\pi,6z)\,dz+\frac{R_\pi^{\,2}}{6}\,K\big(1,\tfrac16\big),
--   $$
--   where $R_\pi$ is `HeckeReciprocal.regularizedL π 1`.
--
--   The first term on the right is the shifted integral. The second is the residue at the pole $w=1$ of $L(\pi,w)$, with its $z$-contour moved to $\operatorname{Re}z=\tfrac{33}{200}$. The third is the double residue at $w=1$, $z=\tfrac16$. The hypotheses $B_p\le a$ and $\beta<a$ keep $s$ in the region where the correction factors are analytic and the Hecke $L$-function of $\eta_S$ has no zero.
--
--   **Formalization Note** The tuned constants appear as `TunedCandidate.ell`, `TunedCandidate.lx`, `TunedCandidate.ly`, `TunedCandidate.h`, `TunedCandidate.zeta`, `TunedCandidate.b`, `TunedCandidate.B`, `TunedCandidate.signal`, and $B_p$ also as `Geometry.boundary TunedCandidate.p`, which equals `TunedCandidate.B`. The source abbreviations `transportBoundary` and `transportShift` are written out as `Geometry.boundary TunedCandidate.p` and `-2/3-TunedCandidate.b/6`, to which they unfold. The remaining definitions are OpenAI's, from the definition bundles of the OpenAI mission on this platform. The namespace opens of the source file that are not available from the definition bundles were omitted, the local finiteness instance was given a name where present, and spaces were inserted after some `<` and `≤` signs so that the statement tokenizes under `import Mathlib`.
-- source:
--   LW56e2, quasi-riemann-improved, commit b83dbbd914c5751acf9bc3389cde58970437278f, lean/Transport/PhysicalAnalytic/Contours.lean, theorem source_ordered_at_height (L301-L318): https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/PhysicalAnalytic/Contours.lean#L301-L318

import Mathlib
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B008
import Definitions.Def_OAIHecke78B016
import Definitions.Def_OAIHecke78B019
import Definitions.Def_OAIHecke78B021
import Definitions.Def_OAIHecke78B022
import Definitions.Def_OAIHecke78B023
import Definitions.Def_OAIHecke78B024
import Definitions.Def_OAIHecke78B026
import Definitions.Def_OAIHecke78B027
import Definitions.Def_OAIHecke78B028
import Definitions.Def_Transport_Geometry
import Definitions.Def_Transport_LocalBounds
import Definitions.Def_Transport_SupportedMass
import Definitions.Def_Transport_TunedCandidate
set_option autoImplicit false

namespace RH.Transport.PhysicalAnalytic.Contours

noncomputable section

open scoped Classical BigOperators Topology

open Complex Set MeasureTheory Filter

open OAI OAI.SevenEighths

open HeckeFamily ProbePhysical ProbeEuler ProbeLocal CompletedGauss

open ProbeFiniteProductBounds ProbeFiniteProductX PrincipalMellinResidues

open PrincipalMellinGrowth ProbeMellinBoundary ProbePrincipalContours

local notation "Id" => Ideal ActualEisensteinCubic.O

local instance : Countable ActualEisensteinCubic.O := ActualEisensteinCubic.latticeCoordEquiv.injective.countable

local instance : Countable Id := ConcretePrimeRowBridge.idealGenerator_injective.countable

theorem source_ordered_at_height {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a e t cw : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z)
    (ha : (Geometry.boundary TunedCandidate.p)≤ a) (hβ : HeckeZeroSupremum.beta< a) (hcw : 1< cw) (he : 0< e)
    (hs1 : (a:ℂ)+t*I≠1) :
    let s : ℂ := (a:ℂ)+t*I
    let K := sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s)
    let π := fixedSourcePrincipal S hS.prime
    verticalIntegral (1/6+e) (fun z => verticalIntegral cw
      (fun w => K w z*LFunction π (6*z)*LFunction π w)) =
    verticalIntegral (1/6+e) (fun z => verticalIntegral (19/20)
      (fun w => K w z*LFunction π (6*z)*LFunction π w)) +
    HeckeReciprocal.regularizedL π 1*verticalIntegral (33/200) (fun z => K 1 z*LFunction π (6*z)) +
    (HeckeReciprocal.regularizedL π 1)^2/6*K 1 (1/6) := by sorry

end

end RH.Transport.PhysicalAnalytic.Contours
