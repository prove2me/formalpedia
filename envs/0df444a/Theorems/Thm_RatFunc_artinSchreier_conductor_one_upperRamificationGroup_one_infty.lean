-- Prove2me | Theorems.Thm_RatFunc_artinSchreier_conductor_one_upperRamificationGroup_one_infty
-- name    : RatFunc.artinSchreier_conductor_one_upperRamificationGroup_one_infty
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-14T10:28:03.637035+00:00
-- url     : https://prove2.me/theorems/ef7e2286-4953-44f8-824c-ec5b91264442
-- title:
--   Slope-one structure of wild inertia at infinity: $I^1/I^{1+} \cong \mathbb{F}_q$ via the Artin–Schreier character, and twists $\rho \otimes \mathcal{L}_\psi(bx)$ with $\mathrm{Sw} < \dim\rho$
-- statement:
--   Let $\mathbb{F}_q$ be a finite field with $q$ elements, $K = \mathbb{F}_q(x)$, and let $L'/K$ be a finite Galois extension with group $G = \mathrm{Gal}(L'/K)$. Suppose that $L'$ contains an Artin–Schreier element of conductor one at infinity, that is, $y \in L'$ with
--
--   $$y^q - y = g, \qquad g \in K, \quad \deg g = 1,$$
--
--   where $\deg g$ is the degree of the numerator minus the degree of the denominator (so $g$ has a simple pole at $\infty$; for example $g = x$). For $\sigma \in G$ the element $a_\sigma = \sigma(y) - y$ lies in $\mathbb{F}_q$, and $\Phi(\sigma) = a_\sigma$ is the Artin–Schreier character of $K(y)/K$. Let $\mathcal{O}_\infty \subset K$ be the valuation ring of the place at infinity, $B'$ its integral closure in $L'$, and $\mathfrak{Q}'$ a nonzero prime ideal of $B'$ with $|B'/\mathfrak{Q}'| = q$ (a place of $L'$ of degree one over $\infty$). Let
--
--   $$G_i = \{\sigma \in G : \sigma(b) - b \in \mathfrak{Q}'^{\,i+1} \text{ for all } b \in B'\} \quad (i \ge 0)$$
--
--   be the lower ramification groups at $\mathfrak{Q}'$ ($G_0$ is the inertia group), $\varphi(m) = \sum_{u=1}^{m} |G_u|/|G_0|$ the Herbrand function, $G^v = G_{\psi(v)}$ with $\psi(v) = \min\{m : v \le \varphi(m)\}$ the upper ramification groups for $v > 0$, and $G^{1+} = \bigcup_{v > 1} G^v$. Then:
--
--   1. $\Phi$ maps $G^1$ onto $\mathbb{F}_q$;
--   2. $G^v$ fixes $y$ for every $v > 1$, so $G^{1+} \subseteq \ker \Phi$;
--   3. every $\sigma \in G^1$ with $\sigma(y) = y$ lies in $G^{1+}$; hence $\Phi$ induces an isomorphism $G^1/G^{1+} \cong \mathbb{F}_q$;
--   4. for every field $k$, every character $\chi : G^1 \to k^\times$ trivial on $G^{1+}$ has the form $\chi = \psi' \circ \Phi$ for an additive character $\psi' : \mathbb{F}_q \to k^\times$;
--   5. let $k$ be a field in which $q$ is invertible, $\psi : \mathbb{F}_q \to k^\times$ a primitive additive character, and $\rho : G \to \mathrm{GL}(V)$ a representation on a nonzero finite-dimensional $k$-vector space with all breaks $\le 1$ at $\mathfrak{Q}'$ ($G^v$ acts trivially for every $v > 1$). Then there is $b \in \mathbb{F}_q$ such that the twist $\rho' = \rho \otimes \mathcal{L}_\psi(b g)$, $\rho'(\sigma) = \psi(b\,a_\sigma)\,\rho(\sigma)$, has Swan conductor
--
--   $$\mathrm{Sw}_{\mathfrak{Q}'}(\rho') = \sum_{u \ge 1} \frac{|G_u|}{|G_0|}\,\bigl(\dim V - \dim V^{G_u}\bigr) < \dim V.$$
--
--   So the slope-one quotient of the wild inertia at a place over infinity is the Artin–Schreier group $\mathbb{F}_q$ of the conductor-one cover, and a representation with all breaks at most one can be twisted by some $\mathcal{L}_\psi(bx)$ to acquire slopes below one. This is the local analysis at $\infty$ behind the Fourier-transform step in Katz's study of exponential sums.
--
--   **Formalization Note**: $K$ is `RatFunc Fq`, $\mathcal{O}_\infty$ is `(RatFunc.inftyValuation Fq).valuationSubring`, $B'$ is `integralClosure (RatFunc.inftyValuation Fq).valuationSubring L'`, $\deg g$ is `g.intDegree`, and $G$ is `L' ≃ₐ[RatFunc Fq] L'` with `[FiniteDimensional (RatFunc Fq) L']` and `[IsGalois (RatFunc Fq) L']`. The families $i \mapsto G_i$ and $v \mapsto G^v$ are arbitrary maps `G : ℕ → Subgroup _` and `Gu : ℚ → Subgroup _` pinned down by the hypotheses `hG` (membership $\sigma \in G_i$ written as `∀ b, ∃ c ∈ Q' ^ (i + 1), (c : L') = σ b - b`) and `hGu` (for $v > 0$, `Gu v = G (sInf {m | v ≤ ∑ u ∈ Finset.range m, |G (u+1)| / |G 0|})`); cardinalities are `Nat.card`. Membership in $G^{1+}$ is written `∃ v : ℚ, 1 < v ∧ σ ∈ Gu v`. In item 4, $\chi$ is a monoid homomorphism `Gu 1 →* kˣ` and $\psi'$ an `AddChar Fq k`. In item 5, $\psi$ is an `AddChar Fq k` with `ψ.IsPrimitive`, `(Fintype.card Fq : k) ≠ 0`, `[Nontrivial V]`, and the twist is any representation `ρ'` with `ρ' σ = ψ (b * a) • ρ σ` whenever `σ y = y + a` (such a `ρ'` exists and is unique); the Swan conductor is a `finsum` over `u : ℕ` whose $u$-th term is the term for $G_{u+1}$, with $\dim V^{G_{u+1}}$ the `finrank` of `Representation.invariants` of `ρ'` restricted to `G (u + 1)`, computed in `ℚ`. The hypotheses are satisfiable: for example $L' = K(y)$ with $y^q - y = x$, which is Galois of degree $q$ and totally ramified at $\infty$, and $\mathfrak{Q}'$ the unique place over $\infty$.
-- source:
--   N. M. Katz, Exponential Sums and Differential Equations, Annals of Mathematics Studies 124, Princeton University Press (1990), Section 7.8 (local structure at $\infty$ for the Fourier transform); upper numbering, Herbrand's theorem and the Swan conductor as in J.-P. Serre, Local Fields, GTM 67, Springer (1979), Chapters IV and VI, and N. M. Katz, Gauss Sums, Kloosterman Sums, and Monodromy Groups, Annals of Mathematics Studies 116, Princeton University Press (1988), Chapter 1

import Mathlib

set_option autoImplicit false

open scoped Classical

theorem RatFunc.artinSchreier_conductor_one_upperRamificationGroup_one_infty
    (Fq : Type) [Field Fq] [Fintype Fq]
    (L' : Type) [Field L'] [Algebra (RatFunc Fq) L'] [FiniteDimensional (RatFunc Fq) L']
    [IsGalois (RatFunc Fq) L']
    (g : RatFunc Fq) (hg : g.intDegree = 1) (y : L')
    (hy : y ^ Fintype.card Fq - y = algebraMap (RatFunc Fq) L' g)
    (Q' : Ideal (integralClosure (RatFunc.inftyValuation Fq).valuationSubring L')) [Q'.IsPrime]
    (hQ' : Q' ≠ ⊥)
    (hdeg : Nat.card (integralClosure (RatFunc.inftyValuation Fq).valuationSubring L' ⧸ Q') =
      Fintype.card Fq)
    (G : ℕ → Subgroup (L' ≃ₐ[RatFunc Fq] L'))
    (hG : ∀ (i : ℕ) (σ : L' ≃ₐ[RatFunc Fq] L'), σ ∈ G i ↔
      ∀ b : integralClosure (RatFunc.inftyValuation Fq).valuationSubring L',
        ∃ c ∈ Q' ^ (i + 1), (c : L') = σ b - b)
    (Gu : ℚ → Subgroup (L' ≃ₐ[RatFunc Fq] L'))
    (hGu : ∀ v : ℚ, 0 < v → Gu v = G (sInf {m : ℕ |
      v ≤ ∑ u ∈ Finset.range m, (Nat.card (G (u + 1)) : ℚ) / Nat.card (G 0)})) :
    (∀ a : Fq, ∃ σ ∈ Gu 1, σ y = y + algebraMap (RatFunc Fq) L' (algebraMap Fq (RatFunc Fq) a)) ∧
    (∀ v : ℚ, 1 < v → ∀ σ ∈ Gu v, σ y = y) ∧
    (∀ σ ∈ Gu 1, σ y = y → ∃ v : ℚ, 1 < v ∧ σ ∈ Gu v) ∧
    (∀ {k : Type} [Field k] (χ : Gu 1 →* kˣ),
      (∀ σ : Gu 1, (∃ v : ℚ, 1 < v ∧ (σ : L' ≃ₐ[RatFunc Fq] L') ∈ Gu v) → χ σ = 1) →
      ∃ ψ' : AddChar Fq k, ∀ (σ : Gu 1) (a : Fq),
        (σ : L' ≃ₐ[RatFunc Fq] L') y = y + algebraMap (RatFunc Fq) L' (algebraMap Fq (RatFunc Fq) a) →
          ((χ σ : kˣ) : k) = ψ' a) ∧
    (∀ {k V : Type} [Field k] [AddCommGroup V] [Module k V] [FiniteDimensional k V] [Nontrivial V]
      (ρ : Representation k (L' ≃ₐ[RatFunc Fq] L') V),
      (∀ v : ℚ, 1 < v → ∀ σ ∈ Gu v, ρ σ = LinearMap.id) →
      ∀ ψ : AddChar Fq k, ψ.IsPrimitive → (Fintype.card Fq : k) ≠ 0 →
      ∃ b : Fq, ∀ ρ' : Representation k (L' ≃ₐ[RatFunc Fq] L') V,
        (∀ (σ : L' ≃ₐ[RatFunc Fq] L') (a : Fq),
          σ y = y + algebraMap (RatFunc Fq) L' (algebraMap Fq (RatFunc Fq) a) → ρ' σ = ψ (b * a) • ρ σ) →
        ∑ᶠ u : ℕ, (Nat.card (G (u + 1)) : ℚ) / Nat.card (G 0) *
          ((Module.finrank k V - Module.finrank k (Representation.invariants (ρ'.comp (G (u + 1)).subtype)) : ℕ) : ℚ) <
          Module.finrank k V) := by sorry
