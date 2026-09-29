-- Prove2me | Theorems.Thm_WLight_qExpansion_sigmaTransport_package
-- name    : WLight.qExpansion_sigmaTransport_package
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.868498+00:00
-- url     : https://prove2.me/theorems/499a7ca1-7d6d-5c57-95c8-a3e4a1718252
-- title:
--   Transport of K-rational q-expansions: polynomials, vanishing, j
-- statement:
--   Fix a positive natural number $N$, an intermediate field $K$ of $\mathbb{C}/\mathbb{Q}$, and a ring homomorphism $\varphi \colon K \to \mathbb{C}$ whose image lies in $K$, i.e. $\varphi(z) \in K$ for every $z \in K$. Let $T$ be a relation between functions $\mathbb{H} \to \mathbb{C}$ subject to the hypothesis `hT`, which pins $T$ down by an equivalence: $T(g,g')$ holds if and only if $g$ and $g'$ are differentiable as maps between the complex model spaces (holomorphy on $\mathbb{H}$) and there exists $m \in \mathbb{N}$ such that (i) $g\Delta^{m}$, read through `UpperHalfPlane.ofComplex`, is periodic of period $N$, is bounded at $i\infty$, and every coefficient of its width-$N$ $q$-expansion `UpperHalfPlane.qExpansion N` lies in $K$; (ii) the same three conditions hold for $g'\Delta^{m}$; and (iii) for every $n$ and every $z \in K$ with $(z : \mathbb{C})$ equal to the $n$-th coefficient of the $q$-expansion of $g\Delta^{m}$, the $n$-th coefficient of the $q$-expansion of $g'\Delta^{m}$ equals $\varphi(z)$. Here $\Delta$ is `ModularForm.discriminant`. Under these assumptions three statements hold simultaneously. First, for every (small) index type $\iota$, all families $g, g' \colon \iota \to (\mathbb{H} \to \mathbb{C})$ with $T(g_i, g'_i)$ for all $i$, and every $R \in \mathrm{MvPolynomial}(\iota, K)$, the relation $T$ holds between the evaluation of $R$ at $g$ with coefficients pushed into $\mathbb{C}$ along $K \hookrightarrow \mathbb{C}$ and the evaluation of $R$ at $g'$ with coefficients pushed along $\varphi$. Second, $T(g,g')$ implies that $g = 0$ if and only if $g' = 0$. Third, any function $jf$ with $jf(\tau) = E_4(\tau)^3/\Delta(\tau)$ for all $\tau \in \mathbb{H}$ satisfies $T(jf, jf)$.
--
--   This packages the three closure properties needed when $q$-expansion coefficients of meromorphic level-$N$ objects are conjugated by a homomorphism of the coefficient field, in the shape used for $K = \mathbb{Q}(\zeta_N)$ and $\varphi$ a power map on roots of unity: stability of the transport relation under $K$-polynomial expressions, detection of identical vanishing, and the fact that the hauptmodul $E_4^3/\Delta$ is its own transport. It is stated over an abstract relation $T$ pinned by an equivalence so that each user may substitute its own copy of the predicate; it feeds the rationality statements for $q$-expansions of functions translated by elements of $\Gamma_0(N)$ on the modular curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WLight_qExpansion_sigmaTransport_package.lean

import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.FieldTheory.IntermediateField.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open Complex Real UpperHalfPlane
open scoped Manifold MatrixGroups ModularForm

theorem WLight.qExpansion_sigmaTransport_package (N : ℕ) [NeZero N]
    (K : IntermediateField ℚ ℂ) (φ : ↥K →+* ℂ) (hφK : ∀ z : ↥K, φ z ∈ K)
    (T : (ℍ → ℂ) → (ℍ → ℂ) → Prop)
    (hT : ∀ g g' : ℍ → ℂ, T g g' ↔
        (MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g ∧ MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g' ∧
          ∃ m : ℕ,
            (Function.Periodic ((g * ModularForm.discriminant ^ m) ∘ UpperHalfPlane.ofComplex) N ∧
              IsBoundedAtImInfty (g * ModularForm.discriminant ^ m) ∧
              ∀ n : ℕ,
                (UpperHalfPlane.qExpansion N (g * ModularForm.discriminant ^ m)).coeff n ∈ K) ∧
            (Function.Periodic ((g' * ModularForm.discriminant ^ m) ∘ UpperHalfPlane.ofComplex) N ∧
              IsBoundedAtImInfty (g' * ModularForm.discriminant ^ m) ∧
              ∀ n : ℕ,
                (UpperHalfPlane.qExpansion N (g' * ModularForm.discriminant ^ m)).coeff n ∈ K) ∧
            ∀ (n : ℕ) (z : ↥K),
              (z : ℂ) = (UpperHalfPlane.qExpansion N (g * ModularForm.discriminant ^ m)).coeff n →
              (UpperHalfPlane.qExpansion N (g' * ModularForm.discriminant ^ m)).coeff n = φ z)) :
    (∀ {ι : Type} (g g' : ι → ℍ → ℂ), (∀ i : ι, T (g i) (g' i)) → ∀ R : MvPolynomial ι ↥K,
        T (MvPolynomial.aeval g (MvPolynomial.map (algebraMap ↥K ℂ) R))
          (MvPolynomial.aeval g' (MvPolynomial.map φ R))) ∧
    (∀ g g' : ℍ → ℂ, T g g' → (g = 0 ↔ g' = 0)) ∧
    ∀ jf : ℍ → ℂ, (∀ τ : ℍ, jf τ = ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ) → T jf jf := by sorry
