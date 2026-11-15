-- Prove2me | Theorems.Thm_RH_Transport_PhysicalHigh_actual_ray_normalizer_inverse
-- name    : RH.Transport.PhysicalHigh.actual_ray_normalizer_inverse
-- status  : Proved
-- author  : @Himan
-- created : 2026-11-15T04:04:35.8927+00:00
-- url     : https://prove2.me/theorems/da80cdc6-444f-4d1f-8235-a3f907cfe62b
-- title:
--   The source normalizer is nonzero and $\lvert\mathcal N(Z)^{-1}\rvert\le CZ^{\nu}$ for any total slot length
-- statement:
--   Throughout, $\mathcal O=\mathbb Z[\zeta_3]$ and all objects are those of OpenAI's family-003 development of the quasi-Riemann hypothesis for Hecke characters of $\mathbb Q(\zeta_3)$.
--
--   **Data.** Let $M$ be a nonzero ideal of $\mathcal O$ and $H$ a subgroup of $(\mathcal O/M)^\times$ containing the image of the global units $\mathcal O^\times$. Let $S$ be a finite set of ideals satisfying the source exclusions (its members are prime, it contains the fixed bad primes, and it has the correction tail property). Let $0<c\le b$, let $\ell_1,\dots,\ell_K>0$ with $\sum_j\ell_j=\ell$, and let $W_1,\dots,W_K:\mathbb R\to\mathbb R$ be smooth, compactly supported, nonnegative, not identically zero, with support in the open interval $(c,b)$. Let $W_0,W_1^\ast$ be Schwartz functions on $\mathbb R$ that are real-valued, nonnegative, not identically zero, and supported in $[a_0,b_0]$ and $[a_1,b_1]$ with $a_0,a_1>0$.
--
--   **The normalizer.** For $Z>0$ let $T_j(Z)$ be the set of prime ideals $P\notin S$ lying in the identity ray class modulo $(M,H)$ (principal ideals with a generator whose residue lies in $H$) with
--   $$
--   \lfloor cZ^{\ell_j}\rfloor<N(P)\le\lfloor bZ^{\ell_j}\rfloor ,
--   $$
--   and put
--   $$
--   m_j(Z)=\sum_{P\in T_j(Z)}W_j\!\Big(\frac{N(P)}{Z^{\ell_j}}\Big)N(P)^{-5/6},\qquad
--   \mathcal N(Z)=c_S\cdot(-1)^K Z^{-\ell/6}\prod_{j=1}^K m_j(Z),
--   $$
--   where $c_S$ is the source residue constant of $W_0,W_1^\ast$ at the modulus $\prod_{P\in S}P$: the product of the Mellin transform of $W_1^\ast$ at $1$, the Mellin transform of the radial Fourier transform of $W_0$ at $\tfrac16$, and $\tfrac16$ times the square of the fixed principal residue of that modulus.
--
--   **Statement.** For every $\nu>0$ there is $C>0$ such that for all sufficiently large $Z$,
--   $$
--   \mathcal N(Z)\ne0\qquad\text{and}\qquad \lvert\mathcal N(Z)^{-1}\rvert\le C\,Z^{\nu}.
--   $$
--
--   The total slot length $\ell$ is a free parameter here; OpenAI's original argument is the case of its fixed total length. In the source the proof combines a lower bound for the ray-class prime masses $m_j(Z)$ with the nonvanishing of $c_S$.
--
--   **Formalization Note** $T_j$ is `ProbeRaySlots.pool (RayQuotient.identityClass M H) S c b (Z^(ell j))`, $m_j$ is `slotMass T (residueWeights W _) j`, the scalar $(-1)^KZ^{-\ell/6}\prod m_j$ is `Probe.principalScalar Finset.univ Z total _`, and $c_S$ is `sourceResidueConstant W0 W1 (∏ P ∈ S, P)`. The second Schwartz function $W_1^\ast$ is the Lean variable `W1`. The constant $C$ may depend on all the data and on $\nu$.
-- source:
--   LW56e2, quasi-riemann-improved, commit b83dbbd914c5751acf9bc3389cde58970437278f, lean/Transport/PhysicalHigh/CubeNormalizer.lean, theorem actual_ray_normalizer_inverse (L22-L41): https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/PhysicalHigh/CubeNormalizer.lean#L22-L41

import Mathlib
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B024
set_option autoImplicit false
open scoped Classical BigOperators Topology ContDiff
open Filter
open OAI OAI.SevenEighths
open HeckeFamily ProbePhysical ProbeRaySlots PrincipalSignalComparison
open PrincipalMellinResidues ProbePrincipalResidueActual
local notation "O" => HeckeFamily.O
noncomputable section

theorem RH.Transport.PhysicalHigh.actual_ray_normalizer_inverse {K : ℕ}
    (M : Ideal O) [NeZero M] [Finite (O ⧸ M)]
    (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
    (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (c b : ℝ) (hc : 0<c) (hcb : c≤b)
    (total : ℝ) (ell : Fin K→ℝ) (hell : ∀j,0<ell j) (hellsum : ∑j,ell j=total)
    (W : Fin K→ℝ→ℝ) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hcompact : ∀j,HasCompactSupport (W j))
    (hsupp : ∀j,Function.support (W j)⊆Set.Ioo c b) (hp : ∀j y,0≤W j y) (hne : ∀j,W j≠0)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hr0 : ∀y,(W0 y).im=0) (hr1 : ∀y,(W1 y).im=0)
    (hp0 : ∀y,0≤(W0 y).re) (hp1 : ∀y,0≤(W1 y).re) (hn0 : W0≠0) (hn1 : W1≠0)
    (nu : ℝ) (hnu : 0<nu) :
    letI : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,
      let T := fun j=>pool (RayQuotient.identityClass M H) S c b (Z^(ell j))
      let normer := sourceResidueConstant W0 W1 (∏P∈S,P)*
        (Probe.principalScalar Finset.univ Z total
          (slotMass T (residueWeights W (fun j=>Z^(ell j)))) : ℂ)
      normer≠0 ∧ ‖normer⁻¹‖≤C*Z^nu := by sorry
