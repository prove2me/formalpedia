-- Prove2me | Theorems.Thm_RH_Transport_PhysicalHigh_actual_nonfloor_cube_norm
-- name    : RH.Transport.PhysicalHigh.actual_nonfloor_cube_norm
-- status  : Proved
-- author  : @Himan
-- created : 2026-11-15T20:03:26.39235+00:00
-- url     : https://prove2.me/theorems/63b6742f-6e18-4bff-accb-22fbc84001a7
-- title:
--   Central cube rows of a dyadic block of non-floor rows, from the source moment bound, at the tuned scales
-- statement:
--   Throughout, $\mathcal O=\mathbb Z[\zeta_3]$, a *Hecke character* is a finite-order Hecke character of $\mathbb Q(\zeta_3)$ in OpenAI's family-003 development, and $\beta$ is the supremum of the real parts of the zeros of the associated Hecke $L$-functions (pole exception excluded, sentinel at $1/2$). Objects named in typewriter font are those of OpenAI's development. The *tuned* constants are those of LW56e2's refinement, from the definition bundle `Transport_TunedCandidate`:
--   $$
--   p=\tfrac{214651}{1250000000},\qquad b=\tfrac{192821}{1562500},\qquad \ell=\tfrac16+p,\qquad l_x=\tfrac{1-\ell-b}2,\qquad l_y=\tfrac{1-\ell+b}2,\qquad h=\tfrac{1+3\ell+b}2,\qquad\zeta_0=\tfrac1{8\cdot10^{12}},
--   $$
--   the tuned boundary $B=\tfrac{11}{12}-\tfrac\ell4=\tfrac78-\tfrac p4$, also written $B_p$, and the signal exponent $\operatorname{sig}(s)=s+\tfrac{l_x}2-1+\tfrac h6=s-\tfrac23-\tfrac b6$. OpenAI's development has $\ell=\tfrac16$ and $b=\tfrac18$, hence $l_x=\tfrac{17}{48}$, $l_y=\tfrac{23}{48}$, boundary $\tfrac78$ and $\operatorname{sig}(s)=s-\tfrac{11}{16}$.
--
--   **Setting.** Let $M$ be a nonzero ideal of $\mathcal O$ and $H\le(\mathcal O/M)^\times$ a subgroup containing the image of the global units. Let $N\in\mathbb N$ be the number of slots and let the real parameters $e,\mathrm{eps},c,b_W,A,R,d_{\min},d_{\max},r_{\min},\tau,\varepsilon,\kappa,\mathrm{cost},\mathrm{mesh},\mathrm{margin},\mathrm{loss}$ satisfy the budget inequalities of the Lean statement, among them $0<e<\tfrac1{1000}$, $0<d_{\min}\le d_{\max}$, $8eR+\kappa\le\varepsilon<r_{\min}\,\mathrm{mesh}$, $2\tau<d_{\min}\,\mathrm{cost}$ and $\tau(2+4\,\mathrm{eps})<\mathrm{loss}$. Let $S$ be a finite set of maximal ideals with the source exclusions and `FirstTail (4e) S`. Let $\ell_1,\dots,\ell_N$ be pairwise distinct slot lengths with $d_{\max}r_{\min}\le\ell_j\le d_{\min}R$, and let $W_j$ be smooth windows supported in $(c,b_W)$ with $|W_j|\le A$. Let $\varphi\ge0$ be a smooth, compactly supported, nonzero test function supported in $(a_0',b_0')$ with $a_0'>0$, and let count parameters for $(M,H)$ at loss $\varepsilon_m>0$ be given. Assume $\sum_j\ell_j=\ell$, $\tfrac7{37}d_{\max}\le\ell$ and $d_{\max}\le1$. Let $n\in\mathbb N$, $\nu>0$, $\mathrm{logCost}>0$, $\tau<\mathrm{heightCost}$, $\mu\ge0$ and $\mathrm{saving}$ be real with the total budget
--   $$
--   (159\varepsilon+\varepsilon_m+R+7\nu)+\mu+\big(26e+(N+8)\mathrm{eps}+\mathrm{loss}+\mathrm{mesh}\cdot\ell\big)+(\mathrm{logCost}+\mathrm{heightCost}+\mathrm{momentCost})+\mathrm{saving}\le\frac3{4\cdot10^{12}} .
--   $$
--   Let $W_0,W_1^\ast$ be Schwartz functions supported in $[a_0,b_0]$ and $[a_1,b_1]$ with $a_0,a_1>0$.
--
--   **Statement.** There is $C>0$ such that for every Hecke character $\eta$ and all sufficiently large $Z$ the following holds. Let $d\in[d_{\min},d_{\max}]$, $0\le v\le h+\zeta_0$ with $d-v\le\mu$, $\tfrac{51}{100}<a\le\tfrac78$, $C_0\ge0$, and let `rows` be a finite set of rows $u\ne1$, supported for the calibration of $S$, with
--   $$
--   Z^{1/100}\le\lVert u\rVert\le Z^{d-\mathrm{margin}},\qquad Z^{v}\le\lVert u\rVert\le2Z^{v}.
--   $$
--   Let $i\le n$ and assume that for every row the detector maximum of its source detector family is at least $a$ at height $3iZ^{\tau}$ and below $a+2e$ at height $3(i+1)Z^{\tau}$. Assume the source moment bound `SourceMomentsAt` for these rows at conductor exponent $d$, level $a$, parameter $0$, constant $C_0Z^{\mathrm{momentCost}}$ and height $Z^{\mathrm{heightCost}}$, at every external point $\tfrac{17}{50}+it_2$ with height vector $t$ bounded by $(3i+1)Z^{\tau}$. Then
--   $$
--   \big\lVert\texttt{finiteCentralCubeRows}\big(\eta;\mathrm{rows};Z^{l_x},Z^{l_y},Z;e,a,(3i+1)Z^{\tau}\big)\big\rVert\le C\,C_0\,N(\mathfrak f_\eta)^{2\,\mathrm{eps}}\,Z^{\operatorname{sig}(B)-\mathrm{saving}} ,
--   $$
--   where $B$ is the tuned boundary and the slot pools are $\mathrm{pool}(\text{identity ray class},S,c,b_W,Z^{\ell_j})$.
--
--   This is the bound for one dyadic block of non-floor rows with common level $a$ and height index $i$: the central cube integral of the block is smaller than the signal at the tuned boundary by the factor $Z^{-\mathrm{saving}}$.
--
--   **Formalization Note** The tuned constants appear as `TunedCandidate.ell`, `TunedCandidate.lx`, `TunedCandidate.ly`, `TunedCandidate.h`, `TunedCandidate.zeta`, `TunedCandidate.b`, `TunedCandidate.B`, `TunedCandidate.signal`, and $B_p$ also as `Geometry.boundary TunedCandidate.p`, which equals `TunedCandidate.B`. The remaining definitions are OpenAI's, from the definition bundles of the OpenAI mission on this platform. The namespace opens of the source file that are not available from the definition bundles were omitted, the local finiteness instance was given a name where present, and spaces were inserted after some `<` and `≤` signs so that the statement tokenizes under `import Mathlib`.
-- source:
--   LW56e2, quasi-riemann-improved, commit b83dbbd914c5751acf9bc3389cde58970437278f, lean/Transport/PhysicalHigh/NonfloorIntegral.lean, theorem actual_nonfloor_cube_norm (L26-L77): https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/PhysicalHigh/NonfloorIntegral.lean#L26-L77

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

namespace RH.Transport.PhysicalHigh

noncomputable section

open scoped Classical BigOperators Topology ContDiff

open Filter Set

open OAI OAI.SevenEighths

open ProbeHighRowFamily

open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary

open ProbeRaySlots HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition

local notation "O" => HeckeFamily.O

variable (M : Ideal O) [NeZero M]

local instance instFiniteQuotientOIdeal_transport_actual_nonfloor_cube_norm : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

theorem actual_nonfloor_cube_norm (N n : ℕ) (e eps c b A R dmin dmax rmin τ ε κ cost mesh margin loss : ℝ)
    (he : 0< e) (he1 : e<1/1000) (heps : 0< eps) (hc : 0< c) (hcb : c≤ b) (hA : 0≤ A)
    (hR : 0≤ R) (hdmin : 0< dmin) (hdmax : 0≤ dmax) (hdRange : dmin≤ dmax) (hrmin : 0< rmin)
    (hτ : 0< τ) (hε : 0< ε) (hκ : 0< κ) (hcost : 0≤ cost) (hmesh : 0< mesh)
    (hbudget : 8*e*R+κ≤ ε) (hgap : ε< rmin*mesh) (hmargin : 0< margin)
    (hheight : 2*τ< dmin*cost) (hloss : τ*(2+4*eps)< loss)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*e) S)
    (hmax : ∀P∈S,P.IsMaximal)
    (ell : Fin N→ℝ) (hell : Function.Injective ell)
    (hello : ∀j,dmax*rmin≤ ell j) (hellhi : ∀j,ell j≤ dmin*R)
    (W : Fin N→ℝ→ℂ)
    (hWs : ∀j,Function.support (W j)⊆Ioo c b) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hWB : ∀j t,‖W j t‖≤ A)
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
      (26*e+(N+8)*eps+loss+mesh*TunedCandidate.ell)+
      (logCost+heightCost+momentCost)+saving≤3/4000000000000)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (counts : ProbeFinalAssembly.CountParameters M H εm) :
    ∃C : ℝ,0< C ∧
    ∀η : Character,∀ᶠZ : ℝ in atTop,
      ∀d : ℝ,dmin≤ d → d≤ dmax → ∀(v a C0 : ℝ),0≤ v → v≤ TunedCandidate.h+TunedCandidate.zeta → d-v≤ μ →
      51/100< a → a≤7/8 → 0≤ C0 → ∀rows : Finset FreeRow,
      (∀u∈rows,u.val≠1 ∧ Z^(1/100:ℝ)≤ rowNorm u ∧
        (calibrationForSet S hmax).residueMonoid u.val≠0 ∧ rowNorm u≤ Z^(d-margin)) →
      (∀u∈rows,Z^v≤ rowNorm u ∧ rowNorm u≤2*Z^v) →
      ∀i : ℕ,i≤ n →
      (∀u∈rows,detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        (3*(i+1:ℕ)*Z^τ)< a+2*e) →
      (∀u∈rows,a≤ detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        ((3*i:ℕ)*Z^τ)) →
      let Y : Fin N→ℝ := fun j=>Z^(ell j)
      let T : Fin N→Finset ProbePhysical.PrimeIdeal := fun j=>pool (RayQuotient.identityClass M H) S c b (Y j)
      (∀t : HeightSpace,((|t.1.1|≤(3*i+1:ℕ)*Z^τ ∧ |t.2|≤(3*i+1:ℕ)*Z^τ) ∧ |t.1.2|≤(3*i+1:ℕ)*Z^τ) →
      SourceMomentsAt M H hH S hS.prime η rows ell W Z d a ε τ dmax b R mesh i
        ((17/50:ℂ)+t.1.2*Complex.I) 0
        (if 2*a-1≤5/6 then counts.cB else counts.cH) (if 2*a-1≤5/6 then counts.kB else counts.kH)
        (C0*Z^momentCost) (Z^heightCost) εm) →
      ‖finiteCentralCubeRows S hS hmax η rows T (nonfloorPoolOutside M H S N c b Y) W Y
        W0 W1 (Z^TunedCandidate.lx) (Z^TunedCandidate.ly) Z e (fun _=>a) (fun _=>(3*i+1:ℕ)*Z^τ)‖≤
        C*C0*(η.modulus.absNorm:ℝ)^(2*eps)*Z^(TunedCandidate.signal TunedCandidate.B-saving) := by sorry

end

end RH.Transport.PhysicalHigh
