-- Prove2me | Theorems.Thm_Polynomial_exists_continuousMulEquiv_galois_maxUnramified_algClosed_geometric
-- name    : Polynomial.exists_continuousMulEquiv_galois_maxUnramified_algClosed_geometric
-- status  : Open
-- author  : @Nickrobbins95
-- created : 2026-11-26T08:58:49.813795+00:00
-- url     : https://prove2.me/theorems/4b3b949a-77c6-547e-92db-0e26e4b955df
-- title:
--   The geometric fundamental group of the affine line over a finite field: $\pi_1^{\mathrm{geo}}(\mathbb{A}^1_{\mathbb{F}_q}) \cong \pi_1(\mathbb{A}^1_{\overline{\mathbb{F}}_q})$
-- statement:
--   Let $\mathbb{F}_q$ be a finite field with $q$ elements and let $k$ be an algebraically closed field that is algebraic over $\mathbb{F}_q$ (so $k$ is an algebraic closure $\overline{\mathbb{F}}_q$).
--
--   For a field $E \in \{\mathbb{F}_q, k\}$ let $E(T)$ be the rational function field, fix an algebraic closure $\overline{E(T)}$, and let $K_U(E) \subset \overline{E(T)}$ be the compositum of all finite Galois extensions $L/E(T)$ in $\overline{E(T)}$ that are unramified over $E[T]$: for every prime $\mathfrak{P}$ of the integral closure $E[T]_L$ of $E[T]$ in $L$, the only $\sigma \in \mathrm{Gal}(L/E(T))$ with $\sigma(b) \equiv b \pmod{\mathfrak{P}}$ for all $b \in E[T]_L$ is $\sigma = 1$. With its Krull topology, $\mathrm{Gal}(K_U(E)/E(T))$ is the étale fundamental group $\pi_1(\mathbb{A}^1_E)$ of the affine line over $E$. Let
--
--   $$\pi_1^{\mathrm{geo}} = \{\sigma \in \mathrm{Gal}(K_U(\mathbb{F}_q)/\mathbb{F}_q(T)) : \sigma(x) = x \text{ for every } x \in K_U(\mathbb{F}_q) \text{ with } x^{q^n} = x \text{ for some } n \ge 1\}$$
--
--   be the subgroup fixing all constants, the geometric fundamental group (the kernel of $\pi_1(\mathbb{A}^1_{\mathbb{F}_q}) \to \mathrm{Gal}(\overline{\mathbb{F}}_q/\mathbb{F}_q)$), with the subspace topology.
--
--   Then there is a field isomorphism $\iota : K_U(k) \to K_U(\mathbb{F}_q)$ such that
--
--   1. $\iota$ extends the inclusion $\mathbb{F}_q[T] \subset k[T]$: $\iota(f) = f$ for every $f \in \mathbb{F}_q[T]$, where on the left $f$ is read in $k[T]$ through $\mathbb{F}_q \subset k$ (in particular $\iota(T) = T$);
--   2. every constant of $K_U(\mathbb{F}_q)$ (every $x$ with $x^{q^n} = x$ for some $n \ge 1$) is $\iota(c)$ for some $c \in k$;
--   3. conjugation by $\iota$ is an isomorphism of topological groups
--
--   $$\mathrm{Gal}(K_U(k)/k(T)) \xrightarrow{\ \sim\ } \pi_1^{\mathrm{geo}}, \qquad \sigma \longmapsto \iota \circ \sigma \circ \iota^{-1}.$$
--
--   So $\pi_1(\mathbb{A}^1_{\overline{\mathbb{F}}_q}) \cong \pi_1^{\mathrm{geo}}(\mathbb{A}^1_{\mathbb{F}_q})$: the fundamental group of the affine line over the algebraic closure, computed directly from $k(T)$, is the geometric part of the arithmetic fundamental group, and the identification is induced by an explicit field isomorphism over $\mathbb{F}_q(T)$ sending $T$ to $T$. This is the case $X = \mathbb{A}^1$ of the fundamental exact sequence $1 \to \pi_1(X_{\overline{\mathbb{F}}_q}) \to \pi_1(X) \to \mathrm{Gal}(\overline{\mathbb{F}}_q/\mathbb{F}_q) \to 1$, and it is what allows cohomology of $\mathbb{A}^1_{\overline{\mathbb{F}}_q}$ (for instance $H^1_c$ with coefficients in a representation of $\pi_1(\mathbb{A}^1_{\mathbb{F}_q})$) to be computed with the arithmetic group and its Frobenius.
--
--   **Formalization Note**: $\mathbb{F}_q$ is `Fq` with `[Field Fq] [Fintype Fq]` and $q$ is `Fintype.card Fq`; $k$ is a field with `[IsAlgClosed k] [Algebra Fq k] [Algebra.IsAlgebraic Fq k]`. $E(T)$ is `RatFunc E`, $E[T]$ is `Polynomial E`, and $\overline{E(T)}$ is `AlgebraicClosure (RatFunc E)`. $K_U(\mathbb{F}_q)$ and $K_U(k)$ are variables `KU`, `KUk` (intermediate fields of `AlgebraicClosure (RatFunc Fq)` over `RatFunc Fq`, resp. of `AlgebraicClosure (RatFunc k)` over `RatFunc k`) with defining equations `hKU`, `hKUk`: an `iSup` over the intermediate fields `L` with `FiniteDimensional`, `IsGalois` and the unramifiedness condition; $E[T]_L$ is `integralClosure (Polynomial E) L` and the congruence $\sigma(b) \equiv b \pmod{\mathfrak{P}}$ is written elementwise as `∃ c ∈ P, (c : L) = g b - b`. The Galois groups are `KU ≃ₐ[RatFunc Fq] KU` and `KUk ≃ₐ[RatFunc k] KUk` with Mathlib's Krull topology instances; $\pi_1^{\mathrm{geo}}$ is a variable `Γ : Subgroup (KU ≃ₐ[RatFunc Fq] KU)` with membership criterion `hΓ`. The conclusion gives `ι : KUk ≃+* KU` with (1) `ι (f.map (algebraMap Fq k)) = f` for `f : Polynomial Fq` (both sides through `algebraMap` into `RatFunc` and then `KUk`, `KU`), (2) every `x : KU` with `x ^ (Fintype.card Fq) ^ n = x`, `0 < n`, is `ι (algebraMap k (RatFunc k) c)` for some `c : k`, and (3) `e : (KUk ≃ₐ[RatFunc k] KUk) ≃ₜ* Γ` (a group isomorphism that is a homeomorphism) with `e σ x = ι (σ (ι.symm x))`. The hypotheses are satisfiable (take `Fq = ZMod 2` and `k = AlgebraicClosure (ZMod 2)`; `KU`, `KUk` and `Γ` are determined by `hKU`, `hKUk` and `hΓ`), and the groups are infinite (Artin–Schreier coverings), so the statement is not vacuous.
-- source:
--   A. Grothendieck, Revêtements étales et groupe fondamental (SGA 1), Lecture Notes in Math. 224, Springer (1971), Exposé V and Exposé IX, §6 (the étale fundamental group and the homotopy exact sequence); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter I, §5; T. Szamuely, Galois Groups and Fundamental Groups, Cambridge Stud. Adv. Math. 117, Cambridge University Press (2009), Section 5.6 (the homotopy exact sequence)

import Mathlib

set_option autoImplicit false

theorem Polynomial.exists_continuousMulEquiv_galois_maxUnramified_algClosed_geometric
    (Fq : Type) [Field Fq] [Fintype Fq]
    (k : Type) [Field k] [IsAlgClosed k] [Algebra Fq k] [Algebra.IsAlgebraic Fq k]
    (KU : IntermediateField (RatFunc Fq) (AlgebraicClosure (RatFunc Fq)))
    (hKU : KU = ⨆ L : {L : IntermediateField (RatFunc Fq) (AlgebraicClosure (RatFunc Fq)) //
        FiniteDimensional (RatFunc Fq) L ∧ IsGalois (RatFunc Fq) L ∧
        ∀ P : Ideal (integralClosure (Polynomial Fq) L), P.IsPrime →
          ∀ g : L ≃ₐ[RatFunc Fq] L,
            (∀ b : integralClosure (Polynomial Fq) L, ∃ c ∈ P, (c : L) = g b - b) → g = 1}, L.1)
    (KUk : IntermediateField (RatFunc k) (AlgebraicClosure (RatFunc k)))
    (hKUk : KUk = ⨆ L : {L : IntermediateField (RatFunc k) (AlgebraicClosure (RatFunc k)) //
        FiniteDimensional (RatFunc k) L ∧ IsGalois (RatFunc k) L ∧
        ∀ P : Ideal (integralClosure (Polynomial k) L), P.IsPrime →
          ∀ g : L ≃ₐ[RatFunc k] L,
            (∀ b : integralClosure (Polynomial k) L, ∃ c ∈ P, (c : L) = g b - b) → g = 1}, L.1)
    (Γ : Subgroup (KU ≃ₐ[RatFunc Fq] KU))
    (hΓ : ∀ g : KU ≃ₐ[RatFunc Fq] KU, g ∈ Γ ↔
      ∀ x : KU, (∃ n : ℕ, 0 < n ∧ x ^ (Fintype.card Fq) ^ n = x) → g x = x) :
    ∃ ι : KUk ≃+* KU,
      (∀ f : Polynomial Fq,
        ι (algebraMap (RatFunc k) KUk (algebraMap (Polynomial k) (RatFunc k) (f.map (algebraMap Fq k)))) =
          algebraMap (RatFunc Fq) KU (algebraMap (Polynomial Fq) (RatFunc Fq) f)) ∧
      (∀ x : KU, (∃ n : ℕ, 0 < n ∧ x ^ (Fintype.card Fq) ^ n = x) →
        ∃ c : k, ι (algebraMap (RatFunc k) KUk (algebraMap k (RatFunc k) c)) = x) ∧
      ∃ e : (KUk ≃ₐ[RatFunc k] KUk) ≃ₜ* Γ,
        ∀ (σ : KUk ≃ₐ[RatFunc k] KUk) (x : KU), (e σ : KU ≃ₐ[RatFunc Fq] KU) x = ι (σ (ι.symm x)) := by
  sorry
