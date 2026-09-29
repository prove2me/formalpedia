-- Prove2me | Theorems.Thm_PDivisibleGroup_exists_basis_padicComplex_tateModule_eq_cyclotomicCharacter_pow_smul_of_hasDimension_of_ringOfIntegers
-- name    : PDivisibleGroup.exists_basis_padicComplex_tateModule_eq_cyclotomicCharacter_pow_smul_of_hasDimension_of_ringOfIntegers
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:58.387243+00:00
-- url     : https://prove2.me/theorems/b5df7370-8b13-503a-a5ae-52aec1245d5a
-- title:
--   Hodge–Tate decomposition of the Tate module of a p-divisible group
-- statement:
--   Let $p$ be a prime, let $\overline{\mathbb Q}_p$ denote the fixed algebraic closure `PadicAlgCl p` of $\mathbb Q_p$ and let $K$ be an intermediate field of $\mathbb Q_p \subseteq \overline{\mathbb Q}_p$ that is finite-dimensional over $\mathbb Q_p$; write $R = \mathcal O_K$ for the subalgebra [`PadicAlgCl.ringOfIntegers p K`](def/PadicAlgCl_RingOfIntegers.html#L11) of elements of $K$ integral over $\mathbb Z_p$. Let $G$ be a $p$-divisible group of height $h$ over $R$, that is, a system of finite free cocommutative Hopf $R$-algebras `level v` with $\operatorname{rank}_R(\mathrm{level}\ v) = p^{vh}$ together with surjective coalgebra maps $\mathrm{level}(v+1) \to \mathrm{level}\ v$ whose kernels are the ideals `torsionIdeal R (level (v+1)) (p ^ v)`, the images of the augmentation ideal under multiplication by $p^v$. Assume $G$ has dimension $n$, i.e. for every $v$ the module `G.Cotangent v` is $R$-linearly isomorphic to $(R/p^vR)^n$. Put $T =$ [`TateModule p (G.Points (PadicAlgCl p))`](def/EllipticCurve_TateModule.html#L15), the group of sequences $(x_v)$ of $\overline{\mathbb Q}_p$-points of $G$ (elements of the direct limit of the point groups of the levels) with $p^v x_v = 0$ and $p\,x_{v+1} = x_v$. Then $n \le h$, and the $\mathbb C_p$-vector space $\mathbb C_p \otimes_{\mathbb Q_p} (\mathbb Q_p \otimes_{\mathbb Z_p} T)$ admits a basis $(b_i)_{i \in \mathrm{Fin}\ h}$ with the following property: whenever $\sigma$ is a $\mathbb Q_p$-algebra automorphism of $\overline{\mathbb Q}_p$ and $\tau$ an $R$-algebra automorphism of $\overline{\mathbb Q}_p$ with the same underlying map, the tensor product of the action of $\sigma$ on $\mathbb C_p$ with the base change to $\mathbb Q_p$ of the componentwise action of $\tau$ on $T$ sends $b_i$ to $\chi_p(\sigma)\, b_i$ for $i < n$ and to $b_i$ for $i \ge n$, where $\chi_p(\sigma) \in \mathbb Z_p^{\times}$ is the value of the cyclotomic character, viewed in $\mathbb C_p$ via $\mathbb Z_p \subseteq \mathbb Q_p \to \mathbb C_p$.
--
--   This is Tate's Hodge–Tate decomposition $T(G) \otimes_{\mathbb Z_p} \mathbb C_p \cong \mathbb C_p(1)^n \oplus \mathbb C_p^{\,h-n}$ as a semilinear $\mathrm{Gal}(\overline{\mathbb Q}_p/K)$-module, together with the inequality $n \le h$ coming from $\dim G + \dim G^{\vee} = h$. It is used to recover the dimension of a $p$-divisible group from its Tate module, and to show that a $p$-divisible group whose Tate module is fixed by inertia has dimension zero.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PDivisibleGroup_exists_basis_padicComplex_tateModule_eq_cyclotomicCharacter_pow_smul_of_hasDimension_of_ringOfIntegers.lean

import Mathlib
import Definitions.Def_PadicComplex_GaloisAction
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_PDivisibleGroup_Dimension
import Definitions.Def_PadicAlgCl_RingOfIntegers

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem PDivisibleGroup.exists_basis_padicComplex_tateModule_eq_cyclotomicCharacter_pow_smul_of_hasDimension_of_ringOfIntegers
    (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    {h : ℕ} (G : PDivisibleGroup (PadicAlgCl.ringOfIntegers p K) p h) {n : ℕ}
    (hn : G.HasDimension n) :
    n ≤ h ∧
    ∃ b : Module.Basis (Fin h) ℂ_[p]
        (ℂ_[p] ⊗[ℚ_[p]] (ℚ_[p] ⊗[ℤ_[p]] TateModule p (G.Points (PadicAlgCl p)))),
      ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
        (τ : PadicAlgCl p ≃ₐ[PadicAlgCl.ringOfIntegers p K] PadicAlgCl p),
        (∀ x : PadicAlgCl p, τ x = σ x) → ∀ i : Fin h,
        TensorProduct.map (PadicComplex.galAlgHom p σ).toLinearMap
            ((G.tateModuleRep (PadicAlgCl p) τ).baseChange ℚ_[p]) (b i) =
          (algebraMap ℚ_[p] ℂ_[p]
              (((cyclotomicCharacter (PadicAlgCl p) p σ.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p])) ^
            (if (i : ℕ) < n then 1 else 0) • b i := by sorry
