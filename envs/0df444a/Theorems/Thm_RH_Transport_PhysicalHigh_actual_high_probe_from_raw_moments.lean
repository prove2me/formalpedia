-- Prove2me | Theorems.Thm_RH_Transport_PhysicalHigh_actual_high_probe_from_raw_moments
-- name    : RH.Transport.PhysicalHigh.actual_high_probe_from_raw_moments
-- status  : Proved
-- author  : @Himan
-- created : 2026-11-15T04:35:15.427202+00:00
-- url     : https://prove2.me/theorems/3747b842-06b9-49af-aec7-767db3f8f9ff
-- title:
--   High-side comparison of the normalized probe with the signal, from raw source moments, at the tuned exponents
-- statement:
--   Throughout, $\mathcal O=\mathbb Z[\zeta_3]$, a *Hecke character* is a finite-order Hecke character of $\mathbb Q(\zeta_3)$ in OpenAI's family-003 development, and $\beta$ is the supremum of the real parts of the zeros of the associated Hecke $L$-functions (pole exception excluded, sentinel at $1/2$). The tuned constants of LW56e2's refinement are the total slot length $\ell$, the row and column exponents $\ell_x,\ell_y$, the conductor exponent $h$, the cushion $\zeta$, the boundary $B=4374785349/5000000000$ and the signal exponent $\operatorname{sig}(s)=s-2147607/3125000$.
--
--   **Setting.** Let $M$ be a nonzero ideal of $\mathcal O$ and $H\le(\mathcal O/M)^\times$ a subgroup containing the image of the global units. Let $S$ be a finite set of maximal ideals with the source exclusions and the first tail property $\mathrm{FirstTail}(4e,S)$. Let $\ell_1,\dots,\ell_N$ be pairwise distinct slot lengths with $\sum_j\ell_j=\ell$ and $d_{\max}r_{\min}\le\ell_j\le d_{\min}R$, and let $W_j$ be smooth, compactly supported, nonzero windows with values in $[0,A]$ and support in $(c,b)$, $0<c\le b$. Let $\varphi$ be a smooth nonnegative nonzero test function supported in $(a_0,b_0)\subset(0,\infty)$ and bounded by $B_0$, and let $W_0,W_1^\ast$ be real nonnegative nonzero Schwartz functions supported in compact intervals of $(0,\infty)$. Let count parameters for $(M,H)$ at loss $\varepsilon_m$ be given.
--
--   **Scalar hypotheses.** The real parameters $e,\mathrm{eps},R,d_{\min},d_{\max},r_{\min},\tau,\varepsilon,\kappa,\mathrm{cost},\mathrm{mesh},\mathrm{margin},\mathrm{loss},\varepsilon_m,\nu,\mu,\mathrm{saving},\sigma$ and the three costs (log, height, moment), together with two further positive parameters $\nu'$ and the dyadic cost, satisfy the positivity and size conditions listed in the formal statement, of which the principal ones are
--   $$
--   0<e<\tfrac1{1000},\qquad 0<d_{\min}<\tfrac1{100},\qquad d_{\min}\le d_{\max}\le1,\qquad \tfrac7{37}d_{\max}\le\ell,\qquad h+\zeta+2\,\mathrm{margin}\le d_{\max},
--   $$
--   $$
--   8eR+\kappa\le\varepsilon\le\tfrac1{1000},\qquad \varepsilon<r_{\min}\cdot\mathrm{mesh},\qquad 4\tau<d_{\min}\cdot\mathrm{cost},\qquad \tau<\tfrac{d_{\min}}2,\qquad \tau(2+4\,\mathrm{eps})<\mathrm{loss},
--   $$
--   the total budget
--   $$
--   (159\varepsilon+\varepsilon_m+R+7\nu)+\mu+\big(26e+(N+8)\mathrm{eps}+\mathrm{loss}+\mathrm{mesh}\cdot\ell\big)+(\text{log}+\text{height}+\text{moment costs})+\mathrm{saving}\le\frac{3}{4\cdot10^{12}},
--   $$
--   and the conditions on the saving exponent $\sigma>0$:
--   $$
--   \sigma+8e+\nu'\le\tfrac1{20},\qquad \sigma+\nu'\le\tfrac1{4000},\qquad \sigma+e\le B\,d_{\max}r_{\min},\qquad \sigma+\nu'+\text{dyadic cost}\le\mathrm{saving}.
--   $$
--   Finally assume
--   $$
--   B\le\beta\le\tfrac78 .
--   $$
--
--   **Statement.** There are an integer $n>0$ and a constant $C>0$ such that for every Hecke character $\eta$ there is $C_t>0$ for which, for all sufficiently large $Z$, the source normalizer $\mathcal N(Z)$ is nonzero and there are two labelings $\mathrm{idx},\mathrm{grid}$ of the free rows by natural numbers with the following properties.
--
--   1. $1\le\mathrm{idx}(u)\le n$ and $\mathrm{grid}(u)\le\lfloor\tfrac{49}{100}/e\rfloor$ for every row $u$.
--
--   2. With $a_u=\tfrac{51}{100}+e\cdot\mathrm{grid}(u)$, the detector maximum of the source detector family of $u$ at height $3\,\mathrm{idx}(u)Z^{\tau}$ lies in $[a_u,a_u+e)$, the detector maximum at height $3(\mathrm{idx}(u)+1)Z^{\tau}$ is less than $a_u+2e$, and if $a_u>\tfrac{51}{100}$ then some $L$-function of that family has a zero $s$, other than the pole exception, with $a_u\le\operatorname{Re}s<a_u+e$ and $|\operatorname{Im}s|\le3\,\mathrm{idx}(u)Z^\tau$.
--
--   3. For every row $u$ with $Z^{1/100}\le\lVert u\rVert<Z^{h+\zeta}$ and nonzero calibration residue, all characters of the ray cube family of $u$ are nonprincipal, their conductors have norm at most a fixed constant times $N(M)\,N(u)$, and the zero maximum of the family at height $3(\mathrm{idx}(u)+1)Z^\tau$ is less than $a_u+2e$.
--
--   4. For every $C_0\ge0$: suppose that for every small dyadic index $k$, every $i\le n$ and every $j\le\lfloor\tfrac{49}{100}/e\rfloor$ for which the set of supported non-floor rows in the $k$-th dyad with labels $(i,j)$ is nonempty, and every height vector $t$ with coordinates bounded by $(3i+1)Z^\tau$, the source moment bound holds for those rows at conductor exponent $\mathrm{dyadConductor}(Z,\mathrm{margin},k)$, level $a=\tfrac{51}{100}+ej$, external point $\tfrac{17}{50}+it_2$, with constant $C_0Z^{\text{moment cost}}$, height $Z^{\text{height cost}}$ and loss $\varepsilon_m$. Then
--   $$
--   \Big\lvert\frac{P_\eta(Z)}{\mathcal N(Z)}-\mathrm{Sig}_{\eta,S}(Z)\Big\rvert\le\Big(C_t+C\,C_0\,N(\mathfrak f_\eta)^{2\,\mathrm{eps}}\Big)Z^{\operatorname{sig}(\beta)-\sigma},
--   $$
--   where $P_\eta$ is the compensated physical probe with the given slots, row scale $Z^{\ell_x}$ and column scale $Z^{\ell_y}$, and $\mathrm{Sig}_{\eta,S}$ is the Hecke signal of the prime-deleted character $\eta_S$ with the source correction and intercept $\operatorname{sig}(0)$.
--
--   This is the high side of the probe comparison with all scalar choices left as parameters: it converts moment bounds on arithmetic fibers into a power saving $Z^{-\sigma}$ against the signal at the zero supremum, with the dependence on the conductor of $\eta$ isolated in the factor $N(\mathfrak f_\eta)^{2\,\mathrm{eps}}$. It is LW56e2's adaptation of OpenAI's `actual_high_probe_from_raw_moments` to the tuned exponents $\ell,\ell_x,\ell_y,h,\zeta,B$.
--
--   **Formalization Note** The normalizer is `sourceResidueConstant W0 W1 (∏ P ∈ S, P) * Probe.principalScalar Finset.univ Z TunedCandidate.ell _`; the detector family of a row is `sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)`; the row band is `rowBand (Z^(1/100)) (Z^(TunedCandidate.h+TunedCandidate.zeta))`; the rows of item 4 are `cubeBinRows (supportedNonfloorRows S hmax _ grid ∩ dyadicRows 1 k) idx grid i j`; the moment bound is `SourceMomentsAt`; the signal is `HeckeSignal.signal (η.excludePrimes S hS.prime) (sourceCorrection η S) (TunedCandidate.signal 0) Z`. Item 1 also records the inequality $(3\,\mathrm{idx}+1)Z^\tau+Z^\tau/2\le(3\,\mathrm{idx}+2)Z^\tau$. The parameter called $\nu'$ above is the Lean variable `nu` and $\nu$ is `ν`. Relative to the source file, spaces were inserted after some `<` and `≤` signs so that the statement tokenizes under `import Mathlib`; the statement is otherwise verbatim.
-- source:
--   LW56e2, quasi-riemann-improved, commit b83dbbd914c5751acf9bc3389cde58970437278f, lean/Transport/PhysicalHigh/HighProbe.lean, theorem actual_high_probe_from_raw_moments (L23-L109): https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/PhysicalHigh/HighProbe.lean#L23-L109

import Mathlib
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B027
import Definitions.Def_Transport_TunedCandidate
set_option autoImplicit false

namespace RH.Transport.PhysicalHigh

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set
open OAI OAI.SevenEighths
open ProbeFinalAssembly
open ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
open ProbeRaySlots HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition
open PrincipalMellinResidues PrincipalSignalComparison ProbePrincipalResidueActual
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

local instance instFiniteQuotientOIdeal_transport_highProbe : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
theorem actual_high_probe_from_raw_moments (N : ℕ) (e eps c b A R dmin dmax rmin τ ε κ cost mesh margin loss : ℝ)
    (he : 0< e) (he1 : e<1/1000) (heps : 0< eps) (hc : 0< c) (hcb : c≤ b) (hA : 0≤ A)
    (hR : 0≤ R) (hdmin : 0< dmin) (hdmax : 0≤ dmax) (hdRange : dmin≤ dmax) (hrmin : 0< rmin)
    (hτ : 0< τ) (hε : 0< ε) (hκ : 0< κ) (hcost : 0≤ cost) (hmesh : 0< mesh)
    (hbudget : 8*e*R+κ≤ ε) (hgap : ε< rmin*mesh) (hmargin : 0< margin)
    (hheight : 2*τ< dmin*cost) (hloss : τ*(2+4*eps)< loss)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*e) S)
    (hmax : ∀P∈S,P.IsMaximal)
    (ell : Fin N→ℝ) (hell : Function.Injective ell)
    (hello : ∀j,dmax*rmin≤ ell j) (hellhi : ∀j,ell j≤ dmin*R)
    (W : Fin N→ℝ→ℝ)
    (hWs : ∀j,Function.support (W j)⊆Ioo c b) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hWB : ∀j t,0≤ W j t ∧ W j t≤ A)
    (hcompact : ∀j,HasCompactSupport (W j)) (hne : ∀j,W j≠0)
    (hellsum : ∑j,ell j=TunedCandidate.ell)
    (hsupply : (7/37:ℝ)*dmax≤ TunedCandidate.ell) (hdmax1 : dmax≤1) (hε1 : ε≤1/1000) (hκ1 : κ≤1)
    (hτzero : τ< dmin/2) (hτheight : 4*τ< dmin*cost)
    (hwbudget : 12*e*((22:ℝ)+2)+8*κ+2*cost≤ ε/2)
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀y,0≤ φ y) (hφne : φ≠0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0< a₀) (hab₀ : a₀≤ b₀) (hB₀ : 0< B₀)
    (hφs : Function.support φ⊆Ioo a₀ b₀) (hφB : ∀y,φ y≤ B₀)
    (εm ν logCost heightCost momentCost : ℝ)
    (hεm : 0< εm) (hν : 0< ν)
    (hlog : 0< logCost) (hMomentHeight : τ< heightCost)
    (μ saving : ℝ) (hμ : 0≤ μ)
    (hfinal : (159*ε+εm+R+7*ν)+μ+
      (26*e+(N+8)*eps+loss+mesh*TunedCandidate.ell)+(logCost+heightCost+momentCost)+saving≤3/4000000000000)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (hr0 : ∀y,(W0 y).im=0) (hr1 : ∀y,(W1 y).im=0)
    (hp0 : ∀y,0≤(W0 y).re) (hp1 : ∀y,0≤(W1 y).re) (hn0 : W0≠0) (hn1 : W1≠0)
    (nu : ℝ) (hnu : 0< nu)
    (dyadCost : ℝ) (hdyadCost : 0< dyadCost)
    (hdmin1 : dmin<1/100) (hconductor : TunedCandidate.h+TunedCandidate.zeta+2*margin≤ dmax)
    (hmuMargin : 2*margin≤ μ)
    (hβ : TunedCandidate.B≤ HeckeZeroSupremum.beta)
    (hceiling : HeckeZeroSupremum.beta≤7/8)
    (sigma : ℝ) (hsigma : 0< sigma)
    (hgeometric : sigma+8*e+nu≤1/20) (hprincipal : sigma+nu≤1/4000)
    (hwindow : sigma+e≤ TunedCandidate.B*(dmax*rmin))
    (hfloorbudget : 26*e+(N+8)*eps+loss+mesh*TunedCandidate.ell+nu+sigma≤1/200)
    (hcentral : sigma+nu+dyadCost≤ saving) (counts : CountParameters M H εm) :
    letI : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∃n : ℕ,0< n ∧ ∃C : ℝ,
      0< C ∧
    ∀η : Character,∃Ct : ℝ,0< Ct ∧ ∀ᶠZ : ℝ in atTop,
      let Yp := fun j=>Z^(ell j)
      let T := fun j=>pool (RayQuotient.identityClass M H) S c b (Yp j)
      let _hT := nonfloorPoolOutside M H S N c b Yp
      let WC : Fin N→ℝ→ℂ := fun j y=>(W j y:ℂ)
      let normer := sourceResidueConstant W0 W1 (∏P∈S,P)*
        (Probe.principalScalar Finset.univ Z TunedCandidate.ell (slotMass T (residueWeights W Yp)) : ℂ)
      normer≠0 ∧ ∃idx grid : FreeRow→ℕ,
      (∀u,1 ≤ idx u ∧ idx u ≤ n ∧ grid u ≤ ⌊(49/100:ℝ)/e⌋₊ ∧
        ((3*idx u+1:ℕ):ℝ)*Z^τ+Z^τ/2≤(3*idx u+2:ℕ)*Z^τ) ∧
      (∀u, let a : ℝ := 51/100+e*grid u
        (51/100:ℝ)≤ a ∧ a≤1 ∧
        a≤ detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) (3*idx u*Z^τ) ∧
        detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) (3*idx u*Z^τ)< a+e ∧
        detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) (3*(idx u+1:ℕ)*Z^τ)< a+2*e ∧
        (51/100< a → ∃j s,LFunction (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u) j) s=0 ∧
          ¬((sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u) j).residue=1 ∧ s=1) ∧
          a≤ s.re ∧ s.re< a+e ∧ |s.im|≤3*idx u*Z^τ)) ∧
      (∀u∈rowBand (Z^(1/100:ℝ)) (Z^(TunedCandidate.h+TunedCandidate.zeta)),
        (calibrationForSet S hmax).residueMonoid u.val≠0 →
        (∀θ,(rayCubeFamily M H hH u θ).residue≠1) ∧
        (∀θ,(rayCubeFamily M H hH u θ).modulus.absNorm≤
          conductorConstant*M.absNorm*(Ideal.span {u.val}:Ideal O).absNorm) ∧
        ∀hnp : ∀θ,(rayCubeFamily M H hH u θ).residue≠1,
        HeckeDetectorZeros.zeroMaximum (rayCubeFamily M H hH u) hnp
          (3*(idx u+1:ℕ)*Z^τ)<(51/100:ℝ)+e*grid u+2*e) ∧
      let rows := supportedNonfloorRows S hmax (rowBand (Z^(1/100:ℝ)) (Z^(TunedCandidate.h+TunedCandidate.zeta))) grid
      ∀C0 : ℝ,0≤ C0 →
      (∀k∈smallDyadicIndices (Z^(TunedCandidate.h+TunedCandidate.zeta)),∀i∈Finset.range (n+1),∀j∈Finset.range (⌊(49/100:ℝ)/e⌋₊+1),
        let rows' := cubeBinRows (rows∩dyadicRows 1 k) idx grid i j
        rows'.Nonempty → ∀t : HeightSpace,
        ((|t.1.1|≤(3*i+1:ℕ)*Z^τ ∧ |t.2|≤(3*i+1:ℕ)*Z^τ) ∧ |t.1.2|≤(3*i+1:ℕ)*Z^τ) →
        SourceMomentsAt M H hH S hS.prime η rows' ell WC Z
          (sourceDyadConductor Z margin k) (51/100+e*j) ε τ dmax b R mesh i
          ((17/50:ℂ)+t.1.2*Complex.I) 0
          (if 2*(51/100+e*j)-1≤5/6 then counts.cB else counts.cH)
          (if 2*(51/100+e*j)-1≤5/6 then counts.kB else counts.kH)
          (C0*Z^momentCost) (Z^heightCost) εm) →
      ‖compensatedPhysicalProbe η (calibrationForSet S hmax) W0 W1
          (fun j=>canonicalSlotSupport (T j)) WC Yp (Z^TunedCandidate.lx) (Z^TunedCandidate.ly) Z/normer-
        HeckeSignal.signal (η.excludePrimes S hS.prime) (sourceCorrection η S) (TunedCandidate.signal 0) Z‖≤
        (Ct+C*C0*(η.modulus.absNorm:ℝ)^(2*eps))*Z^(TunedCandidate.signal HeckeZeroSupremum.beta-sigma) := by sorry

end
end RH.Transport.PhysicalHigh
