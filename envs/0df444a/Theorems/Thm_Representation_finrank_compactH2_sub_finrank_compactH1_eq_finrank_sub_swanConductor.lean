-- Prove2me | Theorems.Thm_Representation_finrank_compactH2_sub_finrank_compactH1_eq_finrank_sub_swanConductor
-- name    : Representation.finrank_compactH2_sub_finrank_compactH1_eq_finrank_sub_swanConductor
-- status  : Open
-- author  : @Nickrobbins95
-- created : 2026-11-25T21:44:27.201631+00:00
-- url     : https://prove2.me/theorems/74a719d8-9072-4d99-9915-1e79e9cb3d44
-- title:
--   Grothendieck–Ogg–Shafarevich formula on the affine line over $\mathbb F_q$: $h^2_c(\mathbb A^1_{\overline{\mathbb F}_q},M)-h^1_c(\mathbb A^1_{\overline{\mathbb F}_q},M)=\dim M-\mathrm{Sw}_\infty(M)$
-- statement:
--   Let $\mathbb F_q$ be a finite field with $q$ elements, $F=\mathbb F_q(x)$ and $A=\mathbb F_q[x]$, so that $U=\operatorname{Spec}A=\mathbb A^1$ is the projective line minus the point at infinity, and let $\mathcal O_\infty\subset F$ be the valuation ring of the place at infinity ($v_\infty(g)=-\deg g$). Fix an algebraic closure $\overline F$ and let $K_U\subset\overline F$ be the compositum of all finite Galois extensions $L/F$ in $\overline F$ that are unramified over $A$: for every prime $\mathfrak P$ of the integral closure $A_L$ of $A$ in $L$, the only $g\in\mathrm{Gal}(L/F)$ with $g(b)\equiv b\pmod{\mathfrak P}$ for all $b\in A_L$ is $g=1$. Thus $\mathrm{Gal}(K_U/F)$ with its Krull topology is $\pi_1(\mathbb A^1_{\mathbb F_q})$, and
--   $$\Gamma=\{g\in\mathrm{Gal}(K_U/F):\ g(x)=x\text{ for every }x\in K_U\text{ with }x^{q^k}=x\text{ for some }k\ge1\}=\mathrm{Gal}(K_U/F\overline{\mathbb F}_q)$$
--   is the geometric fundamental group $\pi_1(\mathbb A^1_{\overline{\mathbb F}_q})$.
--
--   The nonzero primes of the integral closure $R_{\infty,U}$ of $\mathcal O_\infty$ in $K_U$ are the places of $K_U$ over $\infty$. Let $S$ be a set and $\mathfrak P_s$ ($s\in S$) nonzero primes of $R_{\infty,U}$ forming a system of representatives of these primes modulo $\Gamma$ (every one is $g(\mathfrak P_s)$ for some $s$ and $g\in\Gamma$, and $g(\mathfrak P_s)=\mathfrak P_{s'}$ with $g\in\Gamma$ forces $s=s'$); so $S$ is the set of points of $\mathbb P^1_{\overline{\mathbb F}_q}\setminus\mathbb A^1_{\overline{\mathbb F}_q}$, a single point. Let $I_s=\{g:\ g(b)\equiv b\pmod{\mathfrak P_s}\text{ for all }b\in R_{\infty,U}\}$ be the inertia group of $\mathfrak P_s$.
--
--   Let $M_f\subseteq\overline F$ be a finite Galois extension of $F$ unramified over $A$ (in the sense above), that is, a finite étale Galois cover of $\mathbb A^1$, let $G_f$ be a finite group, $\pi:\mathrm{Gal}(K_U/F)\to G_f$ a surjective homomorphism with kernel $\mathrm{Gal}(K_U/M_f)$, and $\iota:\mathrm{Gal}(M_f/F)\to G_f$ the induced isomorphism, $\pi(g)=\iota(g|_{M_f})$. Let $\ell$ be a prime not dividing $q$, $M$ a finite-dimensional $\mathbb F_\ell$-vector space and $\tau$ a representation of $G_f$ on $M$. Through $\pi$, $M$ is a lisse sheaf of $\mathbb F_\ell$-vector spaces on $\mathbb A^1$ trivialized on $M_f$ (every lisse sheaf of finite $\mathbb F_\ell$-vector spaces on $\mathbb A^1$ has this form).
--
--   Its compactly supported cohomology on $\mathbb A^1_{\overline{\mathbb F}_q}$ is computed by continuous cochains of $\Gamma$: $H^2_c(\mathbb A^1_{\overline{\mathbb F}_q},M)\cong M_\Gamma(-1)$, whose dimension is that of the coinvariants $M_\Gamma$ of $\Gamma$ acting by $g\mapsto\tau(\pi g)$, and $H^1_c(\mathbb A^1_{\overline{\mathbb F}_q},M)$ is the first cohomology of the cone of restriction to the boundary: pairs $(c,m)$ of a locally constant $c:\Gamma\to M$ with $c(gh)=c(g)+\tau(\pi g)\,c(h)$ and $m\in M^S$ with $c(g)=\tau(\pi g)\,m_s-m_s$ for $g\in\Gamma\cap I_s$, modulo the pairs $\big(g\mapsto\tau(\pi g)\,m-m,\ (m)_{s\in S}\big)$ with $m\in M$.
--
--   Let $\mathfrak Q_0$ be any place of $M_f$ over $\infty$, that is, a nonzero prime of the integral closure $B$ of $\mathcal O_\infty$ in $M_f$, and for $i\ge0$ let
--   $$G_i=\{\sigma\in\mathrm{Gal}(M_f/F):\ \sigma(b)-b\in\mathfrak Q_0^{\,i+1}\text{ for all }b\in B\}$$
--   be the lower ramification groups at $\mathfrak Q_0$ ($G_0$ is the inertia group), acting on $M$ through $\iota$ and $\tau$. The Swan conductor of $M$ at $\infty$ is
--   $$\mathrm{Sw}_\infty(M)=\sum_{i\ge1}\frac{|G_i|}{|G_0|}\,\bigl(\dim M-\dim M^{G_i}\bigr).$$
--   Then (Grothendieck–Ogg–Shafarevich)
--   $$\dim H^2_c(\mathbb A^1_{\overline{\mathbb F}_q},M)-\dim H^1_c(\mathbb A^1_{\overline{\mathbb F}_q},M)=\dim M-\mathrm{Sw}_\infty(M).$$
--
--   Role: since $H^0_c$ of an affine curve vanishes, this is the Euler–Poincaré formula $\chi_c(\mathbb A^1_{\overline{\mathbb F}_q},M)=\chi_c(\mathbb A^1_{\overline{\mathbb F}_q})\operatorname{rank}M-\mathrm{Sw}_\infty(M)$ with $\chi_c(\mathbb A^1)=1$ (the genus of $\mathbb F_q(x)$ is $0$ and $\mathbb A^1$ has a single point at infinity), and the answer does not depend on the choice of $\mathfrak Q_0$. It is the Euler characteristic input to Weil-type bounds for one-variable exponential sums: with the Swan conductor $\mathrm{Sw}_\infty(\mathcal L_\psi(f))=\deg f$ of an Artin–Schreier sheaf (RatFunc.artinSchreier_lowerRamificationGroup_infty_eq_and_swan_eq_natDegree) and $H^2_c=0$ it gives $h^1_c(\mathbb A^1_{\overline{\mathbb F}_q},\mathcal L_\psi(f))=\deg f-1$.
--
--   **Formalization Note**: $F$ is `RatFunc Fq` and $\overline F$ is `AlgebraicClosure (RatFunc Fq)`; $A$ is `FunctionField.ringOfIntegers Fq (RatFunc Fq)` and $\mathcal O_\infty$ is `(RatFunc.inftyValuation Fq).valuationSubring` (the instance argument `DecidableEq (RatFunc Fq)` is needed to form it). As in the general curve setting, $R_{\infty,U}$ is written `integralClosure (integralClosure (RatFunc.inftyValuation Fq).valuationSubring (RatFunc Fq)) KU` (the inner integral closure is $\mathcal O_\infty$ itself); integral closures in intermediate fields are `integralClosure _ L`. $K_U$, $\Gamma$ and the inertia groups $I_s$ are variables with defining equations `hKU`, `hΓ`, `hI`; congruences mod a prime are written elementwise (`∃ c ∈ P, (c : L) = g b - b`), and $g(\mathfrak P_s)=\mathfrak Q$ is `b ∈ Q ↔ ∃ c ∈ P s, (b : KU) = g c`. $\mathrm{Gal}(K_U/F)$ is `KU ≃ₐ[RatFunc Fq] KU` with Mathlib's Krull topology and continuity of cochains on $\Gamma$ is `IsLocallyConstant`. $M_f$ is an intermediate field of `AlgebraicClosure (RatFunc Fq)` with the same unramifiedness condition as in `hKU` (`hMf`); `hπ` says `π g = 1` iff `g` fixes every element of $K_U$ lying in $M_f$, `hπs` is surjectivity, and `hι` says `π g = ι σ` whenever `g` restricts to `σ` on $M_f$. $\ell\nmid q$ is `¬ l ∣ Fintype.card Fq` and $M$ is a finite `ZMod l`-module. The relative cocycles `Z` and coboundaries `B` are submodules of `(Γ → M) × (S → M)` given by their membership conditions `hZ`, `hB`, and $H^1_c$ is `Z ⧸ B.comap Z.subtype`; $M_\Gamma$ is `Representation.Coinvariants ((τ.comp π).comp Γ.subtype)`. $\mathfrak Q_0$ is a term of `IsDedekindDomain.HeightOneSpectrum (integralClosure (RatFunc.inftyValuation Fq).valuationSubring Mf)`; membership $\sigma\in G_i$ is written out as `∀ b, ∃ c ∈ Q0.asIdeal ^ (i + 1), (c : Mf) = σ b - b` (for $i=0$ the ideal is `Q0.asIdeal`), $|\cdot|$ is `Nat.card` of the corresponding subtype, and $M^{G_i}$ is the intersection of the kernels of `τ (ι σ) - 1` over $\sigma\in G_i$. The Swan sum is a `finsum` over `i : ℕ` whose $i$-th term is the term for $G_{i+1}$ (ideal `Q0.asIdeal ^ (i + 2)`), and the identity is stated in `ℚ`. The hypotheses are satisfiable: take $M_f=F$ (the bottom intermediate field), $G_f$ trivial and $M=\mathbb F_\ell$; then $S$ is a single point and both sides equal $1$.
-- source:
--   N. M. Katz, Gauss Sums, Kloosterman Sums, and Monodromy Groups, Annals of Mathematics Studies 116, Princeton University Press (1988), p. 13 (the Euler–Poincaré formula on $\mathbb A^1_{\overline{\mathbb F}_q}$); M. Raynaud, Caractéristique d'Euler–Poincaré d'un faisceau et cohomologie des variétés abéliennes, Séminaire Bourbaki, exposé 286 (1965); ramification groups and the Swan conductor as in J.-P. Serre, Local Fields, GTM 67, Springer (1979), Chapters IV and VI

import Mathlib

set_option autoImplicit false

theorem Representation.finrank_compactH2_sub_finrank_compactH1_eq_finrank_sub_swanConductor
    (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
    (KU : IntermediateField (RatFunc Fq) (AlgebraicClosure (RatFunc Fq)))
    (hKU : KU = ⨆ L : {L : IntermediateField (RatFunc Fq) (AlgebraicClosure (RatFunc Fq)) //
        FiniteDimensional (RatFunc Fq) L ∧ IsGalois (RatFunc Fq) L ∧
        ∀ P : Ideal (integralClosure (FunctionField.ringOfIntegers Fq (RatFunc Fq)) L), P.IsPrime →
          ∀ g : L ≃ₐ[RatFunc Fq] L,
            (∀ b : integralClosure (FunctionField.ringOfIntegers Fq (RatFunc Fq)) L,
              ∃ c ∈ P, (c : L) = g b - b) → g = 1}, L.1)
    (Γ : Subgroup (KU ≃ₐ[RatFunc Fq] KU))
    (hΓ : ∀ g : KU ≃ₐ[RatFunc Fq] KU, g ∈ Γ ↔
      ∀ x : KU, (∃ k : ℕ, 0 < k ∧ x ^ (Fintype.card Fq) ^ k = x) → g x = x)
    (S : Type)
    (P : S → Ideal (integralClosure (integralClosure (RatFunc.inftyValuation Fq).valuationSubring
      (RatFunc Fq)) KU))
    (hP : ∀ s, (P s).IsPrime ∧ P s ≠ ⊥)
    (hcover : ∀ Q : Ideal (integralClosure (integralClosure (RatFunc.inftyValuation Fq).valuationSubring
        (RatFunc Fq)) KU),
      Q.IsPrime → Q ≠ ⊥ → ∃ s, ∃ g ∈ Γ,
        ∀ b : integralClosure (integralClosure (RatFunc.inftyValuation Fq).valuationSubring (RatFunc Fq)) KU,
          b ∈ Q ↔ ∃ c ∈ P s, (b : KU) = g (c : KU))
    (hdisj : ∀ s s', ∀ g ∈ Γ,
      (∀ b : integralClosure (integralClosure (RatFunc.inftyValuation Fq).valuationSubring (RatFunc Fq)) KU,
        b ∈ P s' ↔ ∃ c ∈ P s, (b : KU) = g (c : KU)) → s = s')
    (I : S → Subgroup (KU ≃ₐ[RatFunc Fq] KU))
    (hI : ∀ s (g : KU ≃ₐ[RatFunc Fq] KU), g ∈ I s ↔
      ∀ b : integralClosure (integralClosure (RatFunc.inftyValuation Fq).valuationSubring (RatFunc Fq)) KU,
        ∃ c ∈ P s, (c : KU) = g (b : KU) - b)
    (Mf : IntermediateField (RatFunc Fq) (AlgebraicClosure (RatFunc Fq)))
    (hMf : FiniteDimensional (RatFunc Fq) Mf ∧ IsGalois (RatFunc Fq) Mf ∧
      ∀ P : Ideal (integralClosure (FunctionField.ringOfIntegers Fq (RatFunc Fq)) Mf), P.IsPrime →
        ∀ g : Mf ≃ₐ[RatFunc Fq] Mf,
          (∀ b : integralClosure (FunctionField.ringOfIntegers Fq (RatFunc Fq)) Mf,
            ∃ c ∈ P, (c : Mf) = g b - b) → g = 1)
    (Gf : Type) [Group Gf] [Finite Gf] (π : (KU ≃ₐ[RatFunc Fq] KU) →* Gf)
    (hπ : ∀ g : KU ≃ₐ[RatFunc Fq] KU, π g = 1 ↔ ∀ x : KU, (x : AlgebraicClosure (RatFunc Fq)) ∈ Mf → g x = x)
    (hπs : Function.Surjective π)
    (ι : (Mf ≃ₐ[RatFunc Fq] Mf) →* Gf)
    (hι : ∀ (g : KU ≃ₐ[RatFunc Fq] KU) (σ : Mf ≃ₐ[RatFunc Fq] Mf),
      (∀ (x : KU) (hx : (x : AlgebraicClosure (RatFunc Fq)) ∈ Mf),
        ((g x : KU) : AlgebraicClosure (RatFunc Fq)) = ((σ ⟨x, hx⟩ : Mf) : AlgebraicClosure (RatFunc Fq))) →
      π g = ι σ)
    (l : ℕ) [Fact l.Prime] (hlq : ¬ l ∣ Fintype.card Fq)
    (M : Type) [AddCommGroup M] [Module (ZMod l) M] [Module.Finite (ZMod l) M]
    (τ : Representation (ZMod l) Gf M)
    (Z : Submodule (ZMod l) ((Γ → M) × (S → M)))
    (hZ : ∀ x : (Γ → M) × (S → M), x ∈ Z ↔
      IsLocallyConstant x.1 ∧ (∀ g h : Γ, x.1 (g * h) = x.1 g + τ (π g) (x.1 h)) ∧
        ∀ s (g : Γ), (g : KU ≃ₐ[RatFunc Fq] KU) ∈ I s → x.1 g = τ (π g) (x.2 s) - x.2 s)
    (B : Submodule (ZMod l) ((Γ → M) × (S → M)))
    (hB : ∀ x : (Γ → M) × (S → M), x ∈ B ↔
      ∃ m : M, (∀ g : Γ, x.1 g = τ (π g) m - m) ∧ ∀ s, x.2 s = m)
    (Q0 : IsDedekindDomain.HeightOneSpectrum
      (integralClosure (RatFunc.inftyValuation Fq).valuationSubring Mf)) :
    (Module.finrank (ZMod l) (Representation.Coinvariants ((τ.comp π).comp Γ.subtype)) : ℚ) -
        Module.finrank (ZMod l) (Z ⧸ B.comap Z.subtype) =
      Module.finrank (ZMod l) M -
        ∑ᶠ i : ℕ,
          (Nat.card {σ : Mf ≃ₐ[RatFunc Fq] Mf //
              ∀ b : integralClosure (RatFunc.inftyValuation Fq).valuationSubring Mf,
                ∃ c ∈ Q0.asIdeal ^ (i + 2), (c : Mf) = σ b - b} : ℚ) /
            (Nat.card {σ : Mf ≃ₐ[RatFunc Fq] Mf //
              ∀ b : integralClosure (RatFunc.inftyValuation Fq).valuationSubring Mf,
                ∃ c ∈ Q0.asIdeal, (c : Mf) = σ b - b} : ℚ) *
          ((Module.finrank (ZMod l) M : ℚ) -
            Module.finrank (ZMod l) ↥(⨅ (σ : Mf ≃ₐ[RatFunc Fq] Mf)
              (_ : ∀ b : integralClosure (RatFunc.inftyValuation Fq).valuationSubring Mf,
                ∃ c ∈ Q0.asIdeal ^ (i + 2), (c : Mf) = σ b - b),
              LinearMap.ker (τ (ι σ) - 1))) := by
  sorry
