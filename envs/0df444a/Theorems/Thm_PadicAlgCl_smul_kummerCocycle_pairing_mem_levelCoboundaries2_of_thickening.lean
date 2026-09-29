-- Prove2me | Theorems.Thm_PadicAlgCl_smul_kummerCocycle_pairing_mem_levelCoboundaries2_of_thickening
-- name    : PadicAlgCl.smul_kummerCocycle_pairing_mem_levelCoboundaries2_of_thickening
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/2e1a4c5f-e108-57bd-b3c0-572e395c40e0
-- title:
--   Thickening: the χ-twisted Kummer cochain is a level coboundary
-- statement:
--   Fix a prime $p$ (as a `Fact`), an integer $N\ge 1$, and a commutative local ring $B$ in which $(p)^N=0$. Write $G=\overline{\mathbb Q}_p\simeq_{\mathbb Q_p}\overline{\mathbb Q}_p$ for the group of $\mathbb Q_p$-algebra automorphisms of `PadicAlgCl p`. The data are: functions $x,z\colon G\to B^\times$ and $y\colon G\to B$; a finite-dimensional intermediate field $F$ of $\overline{\mathbb Q}/\mathbb Q$; hypotheses that $x$ and $z$ are multiplicative and that $y(gh)=x(g)y(h)+y(g)z(h)$, so that $(x,y;0,z)$ is an upper-triangular cocycle package; the level condition that $x(s)=1$, $y(s)=0$, $z(s)=1$ whenever the image of $s$ under [`localGaloisToGlobal p`](def/GaloisRep_CompletionBridge.html#L41) — restriction of scalars to $\mathbb Q$ followed by restriction to $\overline{\mathbb Q}$ — lies in the fixing subgroup of $F$; and the determinant condition that $x(g)z(g)-a\in (p^N)B$ for every $g$ and every natural number $a$ with $g\mu=\mu^a$ for all $\mu$ with $\mu^{p^N}=1$. Further, $t,\eta\in B$ with $t$ in the maximal ideal and $t\mathfrak m=0$; $\chi\colon G\to\mathbb Z$ with $z(g)^2=1+t\eta\chi(g)$; a primitive $p$-th root of unity $\zeta\in\overline{\mathbb Q}_p$; additive maps $\Lambda\colon B/\mathfrak m\to\mathbb Z/p$ and $\pi\colon B\to\mathbb Z/p^N$ with $\pi(tc)=\Lambda(\bar c)\cdot p^{N-1}$ (the value of $\Lambda(\bar c)$ taken in $\mathbb Z/p^N$); and a Kummer datum $a\in\mathbb Q_p^\times$, $\alpha\in\overline{\mathbb Q}_p^\times$ with $a=\alpha^p$ and $g(\alpha)=\zeta^{\Lambda(\overline{\eta\, y(g)z(g)^{-1}})}\alpha$ for all $g\in G$. The conclusion is that the $2$-cochain sending $(g,h)$ to the image of $\chi(g)\cdot\rho(g)\bigl(h(\alpha)/\alpha\bigr)$ — where $h(\alpha)/\alpha$ is `kummerCocycleRoots hα h`, a $p$-th root of unity, $\rho$ is the Kummer representation of $G$ on $\mu_p(\overline{\mathbb Q}_p)$ written additively, and the image is taken along the inclusion $\mu_p(\overline{\mathbb Q}_p)\hookrightarrow\overline{\mathbb Q}_p^\times$ as a map of additive groups — belongs to [`groupCohomology.levelCoboundaries₂`](def/GroupCohomology_ContinuousH2.html#L92) for the homomorphism [`localGaloisToGlobal p`](def/GaloisRep_CompletionBridge.html#L41) and the representation of $G$ on $\overline{\mathbb Q}_p^\times$ given by `Rep.ofAlgebraAutOnUnits ℚ_[p] (PadicAlgCl p)`.
--
--   This is the cochain-level identity underlying the local computation of Wiles's Chapter 1, §1, Proposition 1.1(ii) (also Diamond's Proposition 6.1), carried out over an arbitrary Artinian thickening $B$ with $t\mathfrak m=0$: the $\chi$-twist of the Kummer cocycle of the residual class is killed in level cohomology by an explicit $1$-cochain built from $\pi(y z^{-1})$. It is used by [`PadicAlgCl.exists_isUnit_forall_dvd_valuation_of_thickening`](thm.html#PadicAlgCl.exists_isUnit_forall_dvd_valuation_of_thickening), where the vanishing of this class feeds the norm-residue input to the local deformation argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PadicAlgCl_smul_kummerCocycle_pairing_mem_levelCoboundaries2_of_thickening.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_Kummer
import Definitions.Def_GaloisRep_CompletionBridge

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem PadicAlgCl.smul_kummerCocycle_pairing_mem_levelCoboundaries2_of_thickening
    {B : Type} [CommRing B] [IsLocalRing B] (p N : ℕ) [Fact p.Prime] (hN : 1 ≤ N)
    (hNB : (p : B) ^ N = 0)
    (x z : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) → Bˣ) (y : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) → B)
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hF : FiniteDimensional ℚ F)
    (hxmul : ∀ g h : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p), x (g * h) = x g * x h)
    (hzmul : ∀ g h : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p), z (g * h) = z g * z h)
    (hy : ∀ g h : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p), y (g * h) = (x g : B) * y h + y g * (z h : B))
    (hlev : ∀ s : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p), localGaloisToGlobal p s ∈ F.fixingSubgroup → x s = 1 ∧ y s = 0 ∧ z s = 1)
    (hxz : ∀ (g : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)) (a : ℕ), (∀ μ : PadicAlgCl p, μ ^ p ^ N = 1 → g μ = μ ^ a) →
      (x g : B) * (z g : B) - (a : B) ∈ Ideal.span {((p ^ N : ℕ) : B)})
    (t η : B) (htm : t ∈ IsLocalRing.maximalIdeal B)
    (htk : ∀ m ∈ IsLocalRing.maximalIdeal B, t * m = 0)
    (χ : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) → ℤ) (hχz : ∀ g : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p), (z g : B) * (z g : B) = 1 + t * η * (χ g : B))
    (ζ : PadicAlgCl p) (hζ : IsPrimitiveRoot ζ p)
    (Λ : IsLocalRing.ResidueField B →+ ZMod p) (π : B →+ ZMod (p ^ N))
    (hπ : ∀ c : B, π (t * c) = ((Λ (IsLocalRing.residue B c)).val : ZMod (p ^ N)) * (p : ZMod (p ^ N)) ^ (N - 1))
    (a : ℚ_[p]ˣ) (α : (PadicAlgCl p)ˣ)
    (hα : algebraMap ℚ_[p] (PadicAlgCl p) (a : ℚ_[p]) = (α : PadicAlgCl p) ^ p)
    (hrep : ∀ g : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p), g (α : PadicAlgCl p) =
          ζ ^ (Λ (IsLocalRing.residue B (η * (y g * (((z g)⁻¹ : Bˣ) : B))))).val * (α : PadicAlgCl p)) :
    (fun g : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) × (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) =>
        (MonoidHom.toAdditive (rootsOfUnity p (PadicAlgCl p)).subtype).toIntLinearMap
          ((χ g.1) • (groupCohomology.Kummer.kummerRep ℚ_[p] (PadicAlgCl p) p).ρ g.1
            (Additive.ofMul (groupCohomology.Kummer.kummerCocycleRoots hα g.2))))
      ∈ groupCohomology.levelCoboundaries₂ (localGaloisToGlobal p)
          (Rep.ofAlgebraAutOnUnits ℚ_[p] (PadicAlgCl p)) := by sorry
