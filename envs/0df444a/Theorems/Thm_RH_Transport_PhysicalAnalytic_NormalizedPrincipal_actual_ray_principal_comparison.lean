-- Prove2me | Theorems.Thm_RH_Transport_PhysicalAnalytic_NormalizedPrincipal_actual_ray_principal_comparison
-- name    : RH.Transport.PhysicalAnalytic.NormalizedPrincipal.actual_ray_principal_comparison
-- status  : Proved
-- author  : @Himan
-- created : 2026-11-15T20:04:24.992203+00:00
-- url     : https://prove2.me/theorems/99860211-f086-4bfd-b4e4-a40da2548e88
-- title:
--   Normalized principal row sums approximate the signal, at the tuned scales
-- statement:
--   Throughout, $\mathcal O=\mathbb Z[\zeta_3]$, a *Hecke character* is a finite-order Hecke character of $\mathbb Q(\zeta_3)$ in OpenAI's family-003 development, and $\beta$ is the supremum of the real parts of the zeros of the associated Hecke $L$-functions (pole exception excluded, sentinel at $1/2$). Objects named in typewriter font are those of OpenAI's development. The *tuned* constants are those of LW56e2's refinement, from the definition bundle `Transport_TunedCandidate`:
--   $$
--   p=\tfrac{214651}{1250000000},\qquad b=\tfrac{192821}{1562500},\qquad \ell=\tfrac16+p,\qquad l_x=\tfrac{1-\ell-b}2,\qquad l_y=\tfrac{1-\ell+b}2,\qquad h=\tfrac{1+3\ell+b}2,\qquad\zeta_0=\tfrac1{8\cdot10^{12}},
--   $$
--   the tuned boundary $B=\tfrac{11}{12}-\tfrac\ell4=\tfrac78-\tfrac p4$, also written $B_p$, and the signal exponent $\operatorname{sig}(s)=s+\tfrac{l_x}2-1+\tfrac h6=s-\tfrac23-\tfrac b6$. OpenAI's development has $\ell=\tfrac16$ and $b=\tfrac18$, hence $l_x=\tfrac{17}{48}$, $l_y=\tfrac{23}{48}$, boundary $\tfrac78$ and $\operatorname{sig}(s)=s-\tfrac{11}{16}$.
--
--   **Setting.** Let $M$ be a nonzero ideal of $\mathcal O$ with finite quotient, $H\le(\mathcal O/M)^\times$ a subgroup containing the image of the global units, $\eta$ a Hecke character and $S$ a finite set of ideals with the source exclusions. Let $0<c\le d$, $B_W\ge0$, $\ell_{\min}>0$, and let $\ell_1,\dots,\ell_K\ge\ell_{\min}$ be pairwise distinct with $\sum_j\ell_j=\ell$. Let $W_j$ be smooth, compactly supported real windows with support in $(c,d)$, $0\le W_j\le B_W$, $W_j\ne0$. Let $W_0,W_1^\ast$ be real-valued, nonnegative, nonzero Schwartz functions supported in $[a_0,b_0]$ and $[a_1,b_1]$ with $a_0,a_1>0$. Let $0<e\le\tfrac1{1000}$ and $\nu>0$ with $B_p<\beta+e\le2$.
--
--   **Statement.** There is $C>0$ such that for all sufficiently large $Z$, with $T_j=\mathrm{pool}(\text{identity ray class},S,c,d,Z^{\ell_j})$ and the normalizer
--   $$
--   \mathcal N(Z)=\texttt{sourceResidueConstant}\Big(W_0,W_1^\ast,\prod_{P\in S}P\Big)\cdot\texttt{principalScalar}\big(Z,\ell;\ \text{slot masses of }T\big),
--   $$
--   one has $\mathcal N(Z)\ne0$ and
--   $$
--   \Big\lVert\frac1{\mathcal N(Z)}\sum_{P\in\prod_jT_j}\prod_jW_j\Big(\frac{N(P_j)}{Z^{\ell_j}}\Big)\,\texttt{principalRowIntegral}(\eta,S;P;Z^{l_x},Z^{l_y},Z)-\mathrm{Sig}_{\eta,S}\big(-\tfrac23-\tfrac b6;Z\big)\Big\rVert\le C\Big(Z^{\,\beta-\frac23-\frac b6-\frac1{4000}+\nu}+Z^{\,\beta-\frac23-\frac b6+e-B_p\ell_{\min}}\Big),
--   $$
--   where $\mathrm{Sig}_{\eta,S}(\sigma;Z)$ is `HeckeSignal.signal` of $\eta_S$ with the source correction of $(\eta,S)$ at shift $\sigma$.
--
--   The shift $-\tfrac23-\tfrac b6$ is the one in $\operatorname{sig}$, so both error exponents are $\operatorname{sig}(\beta)$ plus a correction. The statement is the tuned form of OpenAI's Proved theorem `OAI.SevenEighths.ProbePrincipalNormalized.actual_ray_principal_comparison`, which has $\ell=\tfrac16$, $l_x=\tfrac{17}{48}$, $l_y=\tfrac{23}{48}$, the boundary $\tfrac78$ in place of $B_p$, and the saving $\tfrac{17}{48000}$ in place of $\tfrac1{4000}$.
--
--   **Formalization Note** The tuned constants appear as `TunedCandidate.ell`, `TunedCandidate.lx`, `TunedCandidate.ly`, `TunedCandidate.h`, `TunedCandidate.zeta`, `TunedCandidate.b`, `TunedCandidate.B`, `TunedCandidate.signal`, and $B_p$ also as `Geometry.boundary TunedCandidate.p`, which equals `TunedCandidate.B`. The source abbreviations `transportBoundary` and `transportShift` are written out as `Geometry.boundary TunedCandidate.p` and `-2/3-TunedCandidate.b/6`, to which they unfold. The remaining definitions are OpenAI's, from the definition bundles of the OpenAI mission on this platform. The namespace opens of the source file that are not available from the definition bundles were omitted, the local finiteness instance was given a name where present, and spaces were inserted after some `<` and `≤` signs so that the statement tokenizes under `import Mathlib`.
-- source:
--   LW56e2, quasi-riemann-improved, commit b83dbbd914c5751acf9bc3389cde58970437278f, lean/Transport/PhysicalAnalytic/NormalizedPrincipal.lean, theorem actual_ray_principal_comparison (L19-L48): https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/PhysicalAnalytic/NormalizedPrincipal.lean#L19-L48

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

namespace RH.Transport.PhysicalAnalytic.NormalizedPrincipal

noncomputable section

open scoped Classical BigOperators Topology ContDiff

open Complex Filter

open OAI OAI.SevenEighths

open HeckeFamily ProbePhysical CompletedGauss ProbeFiniteProductBounds

open PrincipalMellinResidues PrincipalSignalComparison ProbePrincipalResidueActual ProbeRaySlots

local notation "Id" => Ideal HeckeFamily.O

theorem actual_ray_principal_comparison {K : ℕ}
    (M : Id) [NeZero M] [Finite (HeckeFamily.O ⧸ M)]
    (H : Subgroup (HeckeFamily.O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)
    (η : Character) (S : Finset Id) (hS : SourceExclusions S)
    (c d B ellMin : ℝ) (hc : 0< c) (hd : c≤ d) (hB : 0≤ B) (hmin : 0< ellMin)
    (ell : Fin K→ℝ) (hell : ∀j,ellMin≤ ell j) (hdis : Function.Injective ell)
    (hsum : (∑j,ell j)=TunedCandidate.ell)
    (W : Fin K→ℝ→ℝ) (hW : ∀j,ContDiff ℝ ∞ (W j))
    (hcompact : ∀j,HasCompactSupport (W j))
    (hsupp : ∀j,Function.support (W j)⊆Set.Ioo c d)
    (hWbounds : ∀j y,0≤ W j y ∧ W j y≤ B) (hne : ∀j,W j≠0)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hr0 : ∀y,(W0 y).im=0) (hr1 : ∀y,(W1 y).im=0)
    (hp0 : ∀y,0≤(W0 y).re) (hp1 : ∀y,0≤(W1 y).re) (hn0 : W0≠0) (hn1 : W1≠0)
    (e nu : ℝ) (he : 0< e) (hehi : e≤1/1000) (hnu : 0< nu)
    (ha : (Geometry.boundary TunedCandidate.p)< HeckeZeroSupremum.beta+e) (ha2 : HeckeZeroSupremum.beta+e≤2) :
    letI : NeZero (∏p∈S,p) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∃C : ℝ,0< C ∧ ∀ᶠZ : ℝ in atTop,
      let T := fun j=>pool (RayQuotient.identityClass M H) S c d (Z^(ell j))
      let normer := sourceResidueConstant W0 W1 (∏p∈S,p)*
        (Probe.principalScalar Finset.univ Z TunedCandidate.ell
          (slotMass T (residueWeights W (fun j=>Z^(ell j)))) : ℂ)
      normer≠0 ∧
      ‖(∑P:(∀j,T j),(∏j,(W j ((Ideal.absNorm (P j).val.val:ℝ)/Z^(ell j)):ℂ))*
        principalRowIntegral η S (fun j=>primaryGenerator (P j).val.val)
          W0 W1 (Z^(TunedCandidate.lx:ℝ)) (Z^(TunedCandidate.ly:ℝ)) Z)/normer-
        HeckeSignal.signal (η.excludePrimes S hS.prime) (sourceCorrection η S) (-2/3-TunedCandidate.b/6 : ℝ) Z‖≤
      C*(Z^(HeckeZeroSupremum.beta+(-2/3-TunedCandidate.b/6 : ℝ)-1/4000+nu)+
        Z^(HeckeZeroSupremum.beta+(-2/3-TunedCandidate.b/6 : ℝ)+e-((Geometry.boundary TunedCandidate.p))*ellMin)) := by sorry

end

end RH.Transport.PhysicalAnalytic.NormalizedPrincipal
