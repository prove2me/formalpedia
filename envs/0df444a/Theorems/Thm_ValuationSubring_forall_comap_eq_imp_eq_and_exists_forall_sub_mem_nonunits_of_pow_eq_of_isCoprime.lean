-- Prove2me | Theorems.Thm_ValuationSubring_forall_comap_eq_imp_eq_and_exists_forall_sub_mem_nonunits_of_pow_eq_of_isCoprime
-- name    : ValuationSubring.forall_comap_eq_imp_eq_and_exists_forall_sub_mem_nonunits_of_pow_eq_of_isCoprime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.37934+00:00
-- url     : https://prove2.me/theorems/7d0ae530-6fb4-5330-a2bc-d0060da2858f
-- title:
--   Prime-to-n radicand: unique, totally ramified extension of O
-- statement:
--   Let $F$ and $E$ be fields with $E$ an $F$-algebra, let $n$ be a natural number with $n>0$, and let $\zeta\in F$ be a primitive $n$-th root of unity. Let $a\in E$ and $b\in F$ satisfy $a^{n}=b$ (the image of $b$ under the structure map), and suppose $E$ is generated over $F$ by $a$, i.e. the intermediate field $F(a)$ is all of $E$. Let $O$ be a valuation subring of $F$ which is a discrete valuation ring, let $\varpi\in O$ be irreducible, $u\in O^{\times}$, and $m\in\mathbb{Z}$ coprime to $n$, and assume $b=u\,\varpi^{m}$ as elements of $F$ (integer power). The conclusion has two parts. First, any two valuation subrings $O_1,O_2$ of $E$ whose preimages under $F\to E$ equal $O$ coincide. Second, there exists a valuation subring $O'$ of $E$ with preimage $O$ such that every $e\in O'$ differs from the image of some $f\in O$ by a non-unit of $O'$ (trivial residue extension), and there are $\pi\in O'$ irreducible and $v\in (O')^{\times}$ with the image of $\varpi$ in $E$ equal to $v\,\pi^{n}$ (ramification index $n$).
--
--   This is the classical statement that a Kummer extension $E=F(b^{1/n})$ whose radicand has valuation prime to $n$ is totally ramified at $O$, with a unique extension of the valuation and trivial residue field extension. It is used for the totally ramified supersingular fibres of the covering of modular curves $X_1(Mp)\to X(\Gamma_1(M)\cap\Gamma_0(p))$, via [`ModularCurve.forall_valuationSubring_igusaFunctionFieldX1C_comap_eq_imp_eq_and_exists_of_mem_ssJSet`](thm.html#ModularCurve.forall_valuationSubring_igusaFunctionFieldX1C_comap_eq_imp_eq_and_exists_of_mem_ssJSet).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_forall_comap_eq_imp_eq_and_exists_forall_sub_mem_nonunits_of_pow_eq_of_isCoprime.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ValuationSubring.forall_comap_eq_imp_eq_and_exists_forall_sub_mem_nonunits_of_pow_eq_of_isCoprime
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (n : ℕ) (hn : 0 < n) (ζ : F) (hζ : IsPrimitiveRoot ζ n)
    (a : E) (b : F) (hab : a ^ n = algebraMap F E b)
    (hgen : IntermediateField.adjoin F ({a} : Set E) = ⊤)
    (O : ValuationSubring F) [IsDiscreteValuationRing ↥O]
    (ϖ : ↥O) (hϖ : Irreducible ϖ) (u : (↥O)ˣ) (m : ℤ) (hm : IsCoprime m (n : ℤ))
    (hb : b = ((u : ↥O) : F) * ((ϖ : ↥O) : F) ^ m) :

    (∀ O₁ O₂ : ValuationSubring E,
        O₁.comap (algebraMap F E) = O → O₂.comap (algebraMap F E) = O → O₁ = O₂) ∧

    (∃ O' : ValuationSubring E, O'.comap (algebraMap F E) = O ∧
      (∀ e : ↥O', ∃ f : ↥O, (e : E) - algebraMap F E (f : F) ∈ O'.nonunits) ∧
      (∃ (π : ↥O') (v : (↥O')ˣ), Irreducible π ∧
        algebraMap F E ((ϖ : ↥O) : F) = ((v : ↥O') : E) * ((π : ↥O') : E) ^ n)) := by sorry
