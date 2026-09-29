-- Prove2me | Theorems.Thm_PadicAlgCl_exists_isUnit_forall_dvd_valuation_of_thickening
-- name    : PadicAlgCl.exists_isUnit_forall_dvd_valuation_of_thickening
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:58.387243+00:00
-- url     : https://prove2.me/theorems/65193792-fb11-5883-8f59-4289f9e7f2de
-- title:
--   Socle thickening forces p ∣ vₚ(a) for Kummer data
-- statement:
--   Let $B$ be a finite commutative local ring in which the image of a prime $p$ lies in the maximal ideal, and write $G = \mathrm{Gal}$-group $\bigl(\overline{\mathbb{Q}_p} \simeq_{\mathbb{Q}_p} \overline{\mathbb{Q}_p}\bigr)$ of $\mathbb{Q}_p$-algebra automorphisms of `PadicAlgCl p`. Given maps $x, z : G \to B^\times$ and $y : G \to B$, a finite-dimensional intermediate field $F$ of $\mathbb{Q} \subseteq \overline{\mathbb{Q}}$, assume: $x$ and $z$ are multiplicative; $y(gh) = x(g)\,y(h) + y(g)\,z(h)$; whenever the image of $s$ under [`localGaloisToGlobal p`](def/GaloisRep_CompletionBridge.html#L41) (restrict $s$ to $\mathbb{Q}$-scalars, then restrict to $\overline{\mathbb{Q}}$) lies in the fixing subgroup of $F$, one has $x(s) = 1$, $y(s) = 0$, $z(s) = 1$; $z(\tau) = 1$ for $\tau$ in the image in $G$ of the inertia subgroup of the valuation subring [`padicIntegers p`](def/GaloisRep_CompletionBridge.html#L20) over $\mathbb{Q}_p$ inside its decomposition subgroup; and for all $g$, $n$, $a$, if $g$ raises every $p^n$-th root of unity to the $a$-th power then $x(g)z(g) - a \in (p^n)$ in $B$. Assume further $t \in \mathfrak{m}_B$ with $t\,\mathfrak{m}_B = 0$, that $z(g)^2 - 1 \in (t)$ for all $g$, that $z(g)^2 \neq 1$ for some $g$, and that $\zeta \in \overline{\mathbb{Q}}$ is a primitive $p$-th root of unity. Then there is a unit $\eta \in B$ such that for every additive map $\Lambda$ from the residue field of $B$ to $\mathbb{Z}/p$, every $a \in \mathbb{Q}_p^\times$ and every unit $\alpha$ of `PadicAlgCl p` with $a = \alpha^p$, if $g(\alpha) = (\mathrm{padicEmbedding}\ p\,\zeta)^{\,\Lambda(\overline{\eta\, y(g) z(g)^{-1}})}\,\alpha$ for all $g \in G$ (the exponent being the canonical natural-number representative), then $p$ divides the $p$-adic valuation of $a$ in $\mathbb{Z}$.
--
--   This is the coordinatewise form of the vanishing-of-cup-product step in Wiles' local analysis at $p$ (Proposition 1.1(ii) of his paper): a non-trivial socle thickening of the diagonal character $z$ obstructs Kummer classes of valuation prime to $p$. It is used in the construction of a $p$-power root of unity congruence for $p$-adic Galois representations whose quotient character satisfies $z^2 - 1 \in (t)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PadicAlgCl_exists_isUnit_forall_dvd_valuation_of_thickening.lean

import Mathlib
import Definitions.Def_GaloisRep_CompletionBridge

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem PadicAlgCl.exists_isUnit_forall_dvd_valuation_of_thickening
    {B : Type} [CommRing B] [IsLocalRing B] [Finite B] (p : ℕ) [Fact p.Prime]
    (hpB : (p : B) ∈ IsLocalRing.maximalIdeal B)
    (x z : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) → Bˣ) (y : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) → B)
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hF : FiniteDimensional ℚ F)
    (hxmul : ∀ g h : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p), x (g * h) = x g * x h)
    (hzmul : ∀ g h : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p), z (g * h) = z g * z h)
    (hy : ∀ g h : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p), y (g * h) = (x g : B) * y h + y g * (z h : B))
    (hlev : ∀ s : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p), localGaloisToGlobal p s ∈ F.fixingSubgroup → x s = 1 ∧ y s = 0 ∧ z s = 1)
    (hzI : ∀ τ : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p), τ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] → z τ = 1)
    (hcyc : ∀ (g : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)) (n a : ℕ), (∀ μ : PadicAlgCl p, μ ^ p ^ n = 1 → g μ = μ ^ a) →
      (x g : B) * (z g : B) - (a : B) ∈ Ideal.span {((p ^ n : ℕ) : B)})
    (t : B) (htm : t ∈ IsLocalRing.maximalIdeal B)
    (htk : ∀ m ∈ IsLocalRing.maximalIdeal B, t * m = 0)
    (hsq : ∀ g : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p), (z g : B) * (z g : B) - 1 ∈ Ideal.span {t})
    (hne : ∃ g : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p), (z g : B) * (z g : B) ≠ 1)
    (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p) :
    ∃ η : B, IsUnit η ∧
      ∀ (Λ : IsLocalRing.ResidueField B →+ ZMod p) (a : ℚ_[p]ˣ) (α : (PadicAlgCl p)ˣ),
        algebraMap ℚ_[p] (PadicAlgCl p) (a : ℚ_[p]) = (α : PadicAlgCl p) ^ p →
        (∀ g : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p), g (α : PadicAlgCl p) =
          padicEmbedding p ζ ^ (Λ (IsLocalRing.residue B (η * (y g * (((z g)⁻¹ : Bˣ) : B))))).val * (α : PadicAlgCl p)) →
        (p : ℤ) ∣ Padic.valuation (a : ℚ_[p]) := by sorry
