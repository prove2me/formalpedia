-- Prove2me | Theorems.Thm_RH_Transport_PhysicalHigh_actual_source_moments_from_inputs
-- name    : RH.Transport.PhysicalHigh.actual_source_moments_from_inputs
-- status  : Proved
-- author  : @Himan
-- created : 2026-11-15T04:25:21.650385+00:00
-- url     : https://prove2.me/theorems/0dd747df-2879-4582-9a8b-76f6a0f996ad
-- title:
--   Source moments with constant $C(1+h)^J$ from the two energy inputs
-- statement:
--   Throughout, $\mathcal O=\mathbb Z[\zeta_3]$, a *Hecke character* is a finite-order Hecke character of $\mathbb Q(\zeta_3)$ in OpenAI's family-003 development, and $\beta$ is the supremum of the real parts of the zeros of the associated Hecke $L$-functions (pole exception excluded, sentinel at $1/2$).
--
--   **Data.** Let $F$ be source data, and let $\ell_1,\dots,\ell_N>0$ be pairwise distinct slot lengths. Let $\varepsilon\le\tfrac1{1000}$ and $0<\varepsilon_m\le1$, and assume the slots are fine: $\ell_j\le\mathrm{mesh}(\varepsilon_m)/200$ for all $j$. Let $c_B,k_B,c_H,k_H>0$ be count parameters.
--
--   **Hypothesis.** Assume the two arithmetic energy inputs at loss $\varepsilon_m$: the positive fine source input $\mathrm{PFSI}(F,N,\varepsilon_m,\mathrm{mesh}(\varepsilon_m))$ and the zero-band input with error $\varepsilon_m/4$ (the two conjuncts of the conclusion of `actual_plain_inputs`).
--
--   **Statement.** There is a degree $J\in\mathbb N$, independent of the character, such that for every Hecke character $\eta$ there is $C>0$ for which, for all sufficiently large $Z$, one has $Z>1$ and, for every height $h\ge0$, every finite set of free rows $u$ with $\lVert u\rVert\ge Z^{1/100}$, every $d\ge\tfrac1{200}$, all real $a,\tau,d_{\max}$, slot mesh and bin width, every index $i$ and every $z$ with $\operatorname{Re}z=\tfrac{17}{50}$ and $|\operatorname{Im}z|\le h$, the source moment bound holds with constant
--   $$
--   C\,(1+h)^{J},
--   $$
--   height $h$ and loss $\varepsilon_m$.
--
--   The source moment bound consists of the four moment fields of OpenAI's detector (inverse raw, inverse marked, plain marked, plain unmarked) for every fiber of every batch built from the given rows, the slot widths $\ell_j/d$ and the window $F.w$. The point of the statement is the shape of the constant: it is polynomial in the height with a degree $J$ fixed before the height is chosen. The count parameters used are $(c_B,k_B)$ when $2a-1\le\tfrac56$ and $(c_H,k_H)$ otherwise.
--
--   **Formalization Note** The conclusion is `SourceMomentsAt F.modulus ⊤ le_top F.S F.exclusions.prime η rows ell (fun _ y => (F.w y : ℂ)) Z d a ε τ dmax 2 slotMesh binWidth i z 0 c κ (C*(1+height)^J) height εm`. Distinctness of the slot lengths is `Function.Injective ell`.
-- source:
--   LW56e2, quasi-riemann-improved, commit b83dbbd914c5751acf9bc3389cde58970437278f, lean/Transport/PhysicalHigh/SourceMomentsCore.lean, theorem actual_source_moments_from_inputs (L28-L44): https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/PhysicalHigh/SourceMomentsCore.lean#L28-L44

import Mathlib
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B027
import Definitions.Def_Transport_PhysicalHigh_EnergyMesh
import Definitions.Def_Transport_PhysicalHigh_PositiveFineSourceInput
set_option autoImplicit false
open RH RH.Transport RH.Transport.PhysicalHigh
open scoped Classical BigOperators
open Filter
open OAI OAI.SevenEighths
open HeckeFamily HeckeInverseAmplification ProbeFinalAssembly ProbeHighRowFamily
open Parameters
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentDetectorEnergyInitialState
open CenteredMomentNaturalFixedRaySource
open ProbeDetectorPlainUnmarkedField
noncomputable section

theorem RH.Transport.PhysicalHigh.actual_source_moments_from_inputs {Δ:ℝ}{D:HighData Δ}(F:SourceData D)
    (N:ℕ)(ell:Fin N→ℝ)(hell:∀j,0<ell j)(hinj:Function.Injective ell)
    (ε εm:ℝ)(hε:ε≤1/1000)(hεm:0<εm)(hεm1:εm≤1)
    (hfine:∀j,ell j≤plainMesh εm/200)
    (cB kB cH kH:ℝ)(hcB:0<cB)(hkB:0<kB)(hcH:0<cH)(hkH:0<kH)
    (hinputs:PositiveFineSourceInput F N εm (plainMesh εm) ∧
      (∃degree:ℕ,∃control:Finset (ℕ×ℕ),∀η₀:Character,∃A:ℝ,0<A ∧ ∀ᶠU:ℝ in atTop,
        ZeroAt (internalQ (sourceFixedIdeal F) η₀) (1/4) (9/4) radialSupportUpper
          0 1 2 (εm/4) U degree control A)):
    ∃J:ℕ,∀η:Character,∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,
      1<Z ∧ ∀height:ℝ,0≤height→∀rows:Finset FreeRow,
      (∀u∈rows,Z^(1/100:ℝ)≤rowNorm u)→∀d:ℝ,(1/200:ℝ)≤d→
      ∀a τ dmax slotMesh binWidth:ℝ,∀i:ℕ,∀z:ℂ,z.re=17/50→|z.im|≤height→
      SourceMomentsAt F.modulus ⊤ le_top F.S F.exclusions.prime η rows ell
        (fun _ y=>(F.w y:ℂ)) Z d a ε τ dmax 2 slotMesh binWidth i z 0
        (if 2*a-1≤5/6 then cB else cH) (if 2*a-1≤5/6 then kB else kH)
        (C*(1+height)^J) height εm :=by sorry
