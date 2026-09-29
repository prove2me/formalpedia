-- Prove2me | Theorems.Thm_TwoChartCech_Cover_serrePairingInt_eq_serrePairing
-- name    : TwoChartCech.Cover.serrePairingInt_eq_serrePairing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/ac00c715-9909-5f63-80f4-6a2c33977580
-- title:
--   Chart residue pairing equals the function-field Serre pairing
-- statement:
--   Let $k$ be a field and $F$ a field extension of $k$ such that: every place $v$ of $F/k$ carries canonical local residue data (so a $k$-linear residue $\mathrm{res}_v : F \to \kappa(v)$ is available), $\Omega_{F/k}$ is nontrivial and is generated over $F$ by $d(\text{uniformizer})$ at each place, every nonzero differential and every nonzero element of $F$ has an associated divisor (the latter of degree $0$). Assume the residue theorem `hRT`: for $\omega \ne 0$ and $f \in F$, the sum over all places of the residue terms of $\omega$ against the constant repartition $f$ vanishes. Let $S_0, S_1$ be sets of places with $S_0 \cup S_1$ all places, so that the pairing [`AlgebraicCurve.serrePairing`](def/AlgebraicCurve_SerrePairing.html#L226) is defined on regular differentials against $\check H^1 = L_{S_0 \cap S_1}(0)/\mathrm{im}\,(L_{S_0}(0) \oplus L_{S_1}(0))$, where $L_S(0)$ is the space of elements of $F$ of adic valuation $\le 1$ at all $v \in S$. Let $\mathcal U = (A_0, A_1, A_{01}, \rho_0, \rho_1)$ be a two-chart cover of $k$-algebras, $\iota$ a finite type, and $\Lambda : \iota \to \mathcal U.\mathrm{LaurentChart}$ a family of ring maps $A_{01} \to k((t))$ over $k$, with hypothesis `hv` that the residue sum $\sum_i \mathrm{Res}_{\Lambda_i}$ on $\Omega_{A_{01}/k}$ annihilates the range of the Čech differential of the Kähler sections; $\mathcal U.\mathrm{serrePairingInt}\,\Lambda\,hv$ is the resulting pairing $\check H^0(\mathcal U, \Omega) \times \check H^1(\mathcal U, \mathcal O) \to k$. Assume further: a $k$-algebra map $\psi : A_{01} \to F$ landing in $L_{S_0 \cap S_1}(0)$; a $k$-linear $e_1 : \check H^1(\mathcal U, \mathcal O) \to \check H^1$ with $e_1[s] = [\psi s]$; a $k$-linear $e_\Omega : \check H^0(\mathcal U, \Omega) \to \Omega^{\mathrm{reg}}_{F/k}$; an embedding $p : \iota \hookrightarrow \mathrm{Places}$ with image exactly $S_0^{\mathrm c}$; and the local comparison `hres`: for all $i$, $s \in A_{01}$ and $\omega \in \check H^0(\mathcal U, \Omega)$, $\mathrm{Res}_{\Lambda_i}(s \cdot \rho_0^*(\omega_0))$ equals $\mathrm{Tr}_{\kappa(p i)/k}\,\mathrm{res}_{p i}(\psi(s)\cdot c_{p i}(e_\Omega \omega))$, the residue term of $e_\Omega\omega$ at $p(i)$ against the constant repartition $\psi(s)$. Then for all $\omega$ and all $x \in \check H^1(\mathcal U, \mathcal O)$, the chart pairing $\langle \omega, x\rangle_\Lambda$ equals the function-field pairing $\langle e_\Omega \omega, e_1 x\rangle$.
--
--   This is the fibre-by-fibre comparison between the residue pairing built from finitely many Laurent charts on a two-chart Čech cover and the residue pairing of the function field $F/k$ on $\Omega^{\mathrm{reg}}_{F/k} \times \check H^1(S_0, S_1; 0)$; all geometric input sits in the hypotheses ($e_1$, $e_\Omega$, the place enumeration $p$, and the local residue identity). It transports Serre duality for the function-field pairing to the chart pairing, and is used in the base-change comparison for a two-affine-open cover and in the Hecke computation on modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_TwoChartCech_Cover_serrePairingInt_eq_serrePairing.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoChartCechSerrePairingInt
import Definitions.Def_AlgebraicCurve_SerrePairing

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u w

theorem TwoChartCech.Cover.serrePairingInt_eq_serrePairing
    {k : Type u} [Field k] {F : Type u} [Field F] [Algebra k F]
    [AlgebraicCurve.HasCanonicalLocalResidueKStar k F]
    [∀ v : AlgebraicCurve.Place k F, v.DCoordGenerates] [Nontrivial Ω[F⁄k]]
    [AlgebraicCurve.HasCanonicalDivisor (K := k) (F := F)] [AlgebraicCurve.HasPrincipalDivisors k F]
    (hRT : AlgebraicCurve.ResidueTheorem k F)
    {S₀ S₁ : Set (AlgebraicCurve.Place k F)} (hcover : S₀ ∪ S₁ = Set.univ)
    (𝒰 : TwoChartCech.Cover.{u, u} k) {ι : Type w} [Fintype ι]
    (Λ : ι → 𝒰.LaurentChart) (hv : 𝒰.ResiduesVanishOnCoboundaries Λ)
    (ψ : 𝒰.A01 →ₐ[k] F)
    (hψ : ∀ s : 𝒰.A01, ψ s ∈ AlgebraicCurve.lSpaceOn (S₀ ∩ S₁) (0 : AlgebraicCurve.Divisor k F))
    (e1 : 𝒰.structureSheaf.H1 →ₗ[k] AlgebraicCurve.cechH1 S₀ S₁ (0 : AlgebraicCurve.Divisor k F))
    (he1 : ∀ s : 𝒰.A01, e1 (Submodule.Quotient.mk s) = Submodule.Quotient.mk ⟨ψ s, hψ s⟩)
    (eΩ : 𝒰.kaehler.H0 →ₗ[k] ↥(AlgebraicCurve.regularDifferentials k F))
    (p : ι ↪ AlgebraicCurve.Place k F) (hp : Set.range p = S₀ᶜ)
    (hres : ∀ (i : ι) (s : 𝒰.A01) (ω : 𝒰.kaehler.H0),
      (Λ i).residue (s • 𝒰.kaehler.r0 ω.val.1) =
        AlgebraicCurve.kaehlerResidueTerm ((eΩ ω : ↥(AlgebraicCurve.regularDifferentials k F)) : Ω[F⁄k])
          (AlgebraicCurve.diagonalHom k F (ψ s)) (p i))
    (ω : 𝒰.kaehler.H0) (x : 𝒰.structureSheaf.H1) :
    𝒰.serrePairingInt Λ hv ω x = AlgebraicCurve.serrePairing hRT hcover (eΩ ω) (e1 x) := by sorry
