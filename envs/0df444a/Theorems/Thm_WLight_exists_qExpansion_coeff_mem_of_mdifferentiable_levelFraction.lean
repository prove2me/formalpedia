-- Prove2me | Theorems.Thm_WLight_exists_qExpansion_coeff_mem_of_mdifferentiable_levelFraction
-- name    : WLight.exists_qExpansion_coeff_mem_of_mdifferentiable_levelFraction
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.37934+00:00
-- url     : https://prove2.me/theorems/a6665bad-44cd-5e14-be80-bf84ddc2d50a
-- title:
--   K-rational q-expansion for holomorphic fractions in j and Fricke functions
-- statement:
--   Fix $N \ge 1$. Let $L$ assign to each $\tau \in \mathbb{H}$ a period pair, pinned by the hypothesis that $(L\tau).\omega_1 = \tau$ and $(L\tau).\omega_2 = 1$; let $W$ be a family of functions indexed by $v \in (\mathbb{Z}/N)^2$ pinned pointwise by $W_v(\tau) = (2\pi i)^{-2}\,\wp_{L\tau}\big((\tilde v_0 \tau + \tilde v_1)/N\big)$, where $\tilde v_i$ denotes the natural-number representative of $v_i$; let $\mathrm{fricke}$ be the family pinned by $\mathrm{fricke}_v(\tau) = -\big(E_4(\tau)E_6(\tau)/\Delta(\tau)\big)/2592 \cdot W_v(\tau)$, and let $jf$ be pinned by $jf(\tau) = E_4(\tau)^3/\Delta(\tau)$, with $E_4$, $E_6$, $\Delta$ the Mathlib Eisenstein series and discriminant. Let $K \subseteq \mathbb{C}$ be the intermediate field $\mathbb{Q}\big(e^{2\pi i/N}\big)$. Let $G \colon \mathbb{H} \to \mathbb{C}$ be holomorphic (in the sense of `MDifferentiable` for the trivial complex model on source and target), and let $P, Q$ be polynomials in the variables indexed by $\{*\} \sqcup \{v \in (\mathbb{Z}/N)^2 : v \ne 0\}$, all of whose coefficients lie in $K$. Write $\tilde P, \tilde Q$ for the evaluations of $P, Q$ at the system sending $*$ to $jf$ and $v$ to $\mathrm{fricke}_v$. Assume $\tilde Q \ne 0$ and $G \cdot \tilde Q = \tilde P$, and assume $G$ is integral over $K[j]$ in cleared form: for some $d$ there are polynomials $p_i \in \mathbb{C}[X]$, $i \in \mathrm{Fin}\,d$, with all coefficients in $K$, such that $G(\tau)^d + \sum_{i} p_i(jf(\tau))\,G(\tau)^i = 0$ for every $\tau$. Then there exists $m \in \mathbb{N}$ such that $G \cdot \Delta^m$, precomposed with `UpperHalfPlane.ofComplex`, is periodic of period $N$, the function $G \cdot \Delta^m$ is bounded as $\operatorname{Im}\tau \to \infty$, and every coefficient of its width-$N$ $q$-expansion lies in $K$.
--
--   This is the rationality statement for $q$-expansions of modular functions of level $N$ built from the $j$-invariant and the Fricke functions, in the shape needed for a $q$-expansion-principle argument: a holomorphic function expressed as a $K$-rational fraction in $j$ and the $f_v$, and integral over $K[j]$, acquires after multiplication by a power of $\Delta$ a width-$N$ Fourier expansion with coefficients in $\mathbb{Q}(\zeta_N)$. It is used in the construction of $\mathbb{Q}(\zeta_N)$-rational bases of spaces of cusp forms and in the comparison of $q$-expansion coefficients under Galois action on modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WLight_exists_qExpansion_coeff_mem_of_mdifferentiable_levelFraction.lean

import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.Geometry.Manifold.Notation
import Mathlib.FieldTheory.IntermediateField.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open Complex Real UpperHalfPlane
open scoped Manifold MatrixGroups ModularForm

theorem WLight.exists_qExpansion_coeff_mem_of_mdifferentiable_levelFraction
    (N : ℕ) [NeZero N]
    (L : ℍ → PeriodPair) (hL : ∀ τ : ℍ, (L τ).ω₁ = (τ : ℂ) ∧ (L τ).ω₂ = 1)
    (W : (Fin 2 → ZMod N) → ℍ → ℂ)
    (hW : ∀ (v : Fin 2 → ZMod N) (τ : ℍ), W v τ = ((2 * (Real.pi : ℂ) * Complex.I) ^ 2)⁻¹ *
      PeriodPair.weierstrassP (L τ) ((((v 0).val : ℂ) * (τ : ℂ) + ((v 1).val : ℂ)) / (N : ℂ)))
    (fricke : (Fin 2 → ZMod N) → ℍ → ℂ)
    (hfricke : ∀ (v : Fin 2 → ZMod N) (τ : ℍ), fricke v τ =
      -(ModularForm.E₄ τ * ModularForm.E₆ τ / ModularForm.discriminant τ) / 2592 * W v τ)
    (jf : ℍ → ℂ)
    (hjf : ∀ τ : ℍ, jf τ = ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ)
    (K : IntermediateField ℚ ℂ)
    (hK : K = IntermediateField.adjoin ℚ
      {Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ))})
    {G : ℍ → ℂ} (hG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G)
    (P Q : MvPolynomial (Option {v : Fin 2 → ZMod N // v ≠ 0}) ℂ)
    (hPK : ∀ m, P.coeff m ∈ K) (hQK : ∀ m, Q.coeff m ∈ K)
    (hQ0 : MvPolynomial.aeval (fun o : Option {v : Fin 2 → ZMod N // v ≠ 0} =>
      o.elim jf fun v => fricke v.1) Q ≠ 0)
    (hGQ : G * MvPolynomial.aeval (fun o : Option {v : Fin 2 → ZMod N // v ≠ 0} =>
        o.elim jf fun v => fricke v.1) Q =
      MvPolynomial.aeval (fun o : Option {v : Fin 2 → ZMod N // v ≠ 0} =>
        o.elim jf fun v => fricke v.1) P)
    (hint : ∃ (d : ℕ) (p : Fin d → Polynomial ℂ), (∀ (i : Fin d) (n : ℕ), (p i).coeff n ∈ K) ∧
      ∀ τ : ℍ, G τ ^ d + ∑ i : Fin d, (p i).eval (jf τ) * G τ ^ (i : ℕ) = 0) :
    ∃ m : ℕ, Function.Periodic ((G * ModularForm.discriminant ^ m) ∘ UpperHalfPlane.ofComplex) N ∧
      IsBoundedAtImInfty (G * ModularForm.discriminant ^ m) ∧
      ∀ n : ℕ, (UpperHalfPlane.qExpansion N (G * ModularForm.discriminant ^ m)).coeff n ∈ K := by sorry
