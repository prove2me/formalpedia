-- Prove2me | Theorems.Thm_RH_Transport_PhysicalTail_transport_canonical_probe_minus_central
-- name    : RH.Transport.PhysicalTail.transport_canonical_probe_minus_central
-- status  : Proved
-- author  : @Himan
-- created : 2026-11-15T20:03:26.82783+00:00
-- url     : https://prove2.me/theorems/4072dc8e-48e8-448d-a6a0-3654380d6d99
-- title:
--   The compensated probe minus its principal pool and finite physical rows, at the tuned scales
-- statement:
--   Throughout, $\mathcal O=\mathbb Z[\zeta_3]$, a *Hecke character* is a finite-order Hecke character of $\mathbb Q(\zeta_3)$ in OpenAI's family-003 development, and $\beta$ is the supremum of the real parts of the zeros of the associated Hecke $L$-functions (pole exception excluded, sentinel at $1/2$). Objects named in typewriter font are those of OpenAI's development. The *tuned* constants are those of LW56e2's refinement, from the definition bundle `Transport_TunedCandidate`:
--   $$
--   p=\tfrac{214651}{1250000000},\qquad b=\tfrac{192821}{1562500},\qquad \ell=\tfrac16+p,\qquad l_x=\tfrac{1-\ell-b}2,\qquad l_y=\tfrac{1-\ell+b}2,\qquad h=\tfrac{1+3\ell+b}2,\qquad\zeta_0=\tfrac1{8\cdot10^{12}},
--   $$
--   the tuned boundary $B=\tfrac{11}{12}-\tfrac\ell4=\tfrac78-\tfrac p4$, also written $B_p$, and the signal exponent $\operatorname{sig}(s)=s+\tfrac{l_x}2-1+\tfrac h6=s-\tfrac23-\tfrac b6$. OpenAI's development has $\ell=\tfrac16$ and $b=\tfrac18$, hence $l_x=\tfrac{17}{48}$, $l_y=\tfrac{23}{48}$, boundary $\tfrac78$ and $\operatorname{sig}(s)=s-\tfrac{11}{16}$.
--
--   **Setting.** Let $M$ be a nonzero ideal of $\mathcal O$ and $H\le(\mathcal O/M)^\times$ a subgroup containing the image of the global units. Let $K\in\mathbb N$ and let $e,\delta,a,b_W,B_W,\zeta,\mathrm{saving}$ be real with $0<e<\tfrac1{1000}$, $0<\delta\le\tfrac12$, $\zeta>0$, $a,b_W>0$, $B_W\ge0$. Assume $B\le\beta$, where $B$ is the tuned boundary. Let $S$ be a finite set of maximal ideals with the source exclusions and the first-tail property `FirstTail (1/4) S`, and let $W_0,W_1^\ast$ be Schwartz functions supported in $[a_0,b_0]$ and $[a_1,b_1]$ with $a_0,a_1>0$.
--
--   **Statement.** There is $C>0$ such that for every Hecke character $\eta$, every $Z\ge1$, all slot sets $T_1,\dots,T_K$ of prime ideals outside $S$ whose tuples have pairwise distinct entries, all slot lengths $\lambda_i\ge0$ with $\sum_i\lambda_i=\ell$, and all windows $W_i$ supported in $[a,b_W]$ with $|W_i|\le B_W$,
--   $$
--   \Big\lVert \mathrm{Probe}_\eta(Z)-\mathrm{Pool}_\eta(Z)-\mathrm{Rows}_\eta(Z)\Big\rVert\le C\,N(\mathfrak f_\eta)^{\delta}\Big(Z^{\operatorname{sig}(\beta)-\frac1{20}+8e}+Z^{-\mathrm{saving}}\Big).
--   $$
--   Here $\mathrm{Probe}_\eta$ is the compensated physical probe with slot scales $Z^{\lambda_i}$ and outer scales $Z^{l_x},Z^{l_y}$, $\mathrm{Pool}_\eta$ is `principalPhysicalPool` at the same scales, and $\mathrm{Rows}_\eta$ is `finitePhysicalRows` over the row band $Z^{1/100}\le\lVert u\rVert<Z^{h+\zeta}$.
--
--   The statement says that, up to the displayed error, the probe is its principal part plus the contribution of the rows in a finite band. The rows of norm below $Z^{1/100}$ and above $Z^{h+\zeta}$ are the small and large tails, and both are absorbed in the error.
--
--   **Formalization Note** The tuned constants appear as `TunedCandidate.ell`, `TunedCandidate.lx`, `TunedCandidate.ly`, `TunedCandidate.h`, `TunedCandidate.zeta`, `TunedCandidate.b`, `TunedCandidate.B`, `TunedCandidate.signal`, and $B_p$ also as `Geometry.boundary TunedCandidate.p`, which equals `TunedCandidate.B`. The remaining definitions are OpenAI's, from the definition bundles of the OpenAI mission on this platform. The namespace opens of the source file that are not available from the definition bundles were omitted, the local finiteness instance was given a name where present, and spaces were inserted after some `<` and `≤` signs so that the statement tokenizes under `import Mathlib`.
-- source:
--   LW56e2, quasi-riemann-improved, commit b83dbbd914c5751acf9bc3389cde58970437278f, lean/Transport/PhysicalTail/CanonicalReduction.lean, theorem transport_canonical_probe_minus_central (L19-L36): https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/PhysicalTail/CanonicalReduction.lean#L19-L36

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

namespace RH.Transport.PhysicalTail

noncomputable section

open scoped Classical BigOperators

open MeasureTheory Set

open OAI OAI.SevenEighths

open ProbeHighRowFamily

open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary CompletedGauss

local notation "O" => HeckeFamily.O

theorem transport_canonical_probe_minus_central (K : ℕ) (e δ a b B ζ saving : ℝ)
    (he : 0< e) (he' : e<1/1000) (hδ : 0< δ) (hδ' : δ≤1/2) (hζ : 0< ζ)
    (ha : 0< a) (hb : 0< b) (hB : 0≤ B) (hβ : TunedCandidate.B≤ HeckeZeroSupremum.beta)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0< C ∧ ∀(η : Character) (Z : ℝ),1≤ Z →
      ∀(T : Fin K→Finset HeckeInverseAmplification.PrimeIdeal) (_hT : ∀i P,P∈T i→P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      ∀length : Fin K→ℝ,(∀i,0≤ length i) → (∑i,length i)=TunedCandidate.ell →
      ∀W : Fin K→ℝ→ℂ,(∀i,Function.support (W i)⊆Icc a b) → (∀i y,‖W i y‖≤ B) →
      ‖compensatedPhysicalProbe η (calibrationForSet S hmax) W0 W1
          (fun i=>canonicalSlotSupport (T i)) W (fun i=>Z^(length i)) (Z^TunedCandidate.lx) (Z^TunedCandidate.ly) Z-
        principalPhysicalPool η S T W (fun i=>Z^(length i)) W0 W1 (Z^TunedCandidate.lx) (Z^TunedCandidate.ly) Z-
        finitePhysicalRows S hmax η (rowBand (Z^(1/100:ℝ)) (Z^(TunedCandidate.h+ζ))) T W (fun i=>Z^(length i))
          W0 W1 (Z^TunedCandidate.lx) (Z^TunedCandidate.ly) Z‖≤
        C*(η.modulus.absNorm:ℝ)^δ*(Z^(TunedCandidate.signal HeckeZeroSupremum.beta-1/20+8*e)+Z^(-saving)) := by sorry

end

end RH.Transport.PhysicalTail
