-- Prove2me | Theorems.Thm_WeilConjectures_exists_qladic_lower_half_cohomology_of_ge_two
-- name    : WeilConjectures.exists_qladic_lower_half_cohomology_of_ge_two
-- status  : Open
-- author  : @pageman
-- created : 2026-11-23T23:37:38.301715+00:00
-- url     : https://prove2.me/theorems/8c1d07aa-9d5d-4a3c-a26c-aec694f9aed2
-- title:
--   Lower-Half Rational $\mathbb{Q}_\ell$-Adic Cohomology ($1 \le i \le n$) with Middle Duality and Purity ($n \ge 2$, $\ell \ne p$)
-- statement:
--   Let $p$ be a prime, $k$ a finite field of characteristic $p$ with cardinality $q = |k|$, $f : X \to \operatorname{Spec} k$ a smooth, projective, geometrically irreducible morphism of relative dimension $n \ge 2$, and $\ell \ne p$ a prime. Then there exist finite-dimensional $\mathbb{Q}_\ell$-vector spaces $V_i$ ($i \in \mathbb{N}$), $\mathbb{Q}_\ell$-linear Frobenius automorphisms $F_i : V_i \xrightarrow{\sim} V_i$, and a single nondegenerate middle-degree bilinear pairing $B_{\mathrm{mid}} : V_n \times V_n \to \mathbb{Q}_\ell$ satisfying:
--
--   1. **Lower-half Grothendieck–Lefschetz trace formula:** For every integer $m \ge 1$,
--   $$N_m(X) = 1 + q^{nm} + (-1)^n \operatorname{Tr}_{\mathbb{Q}_\ell}(F_n^m) + \sum_{i=1}^{n-1} (-1)^i \bigl(\operatorname{Tr}_{\mathbb{Q}_\ell}(F_i^m) + q^{nm} \operatorname{Tr}_{\mathbb{Q}_\ell}(F_i^{-m})\bigr).$$
--   2. **Middle-degree Poincaré duality:** $B_{\mathrm{mid}}(F_n x, F_n y) = q^n B_{\mathrm{mid}}(x, y)$ for all $x, y \in V_n$, and $B_{\mathrm{mid}}$ is nondegenerate on both sides.
--   3. **Lower-half purity ($1 \le i < n$):** For every $1 \le i < n$, there exists a monic integer polynomial $W_i \in \mathbb{Z}[X]$ such that $W_i(F_i) = 0$ and every complex root $z \in \mathbb{C}$ of $W_i$ satisfies $|z| = q^{i/2}$.
--   4. **Middle-degree Deligne upper weight bound:** There exists a monic integer polynomial $W_n \in \mathbb{Z}[X]$ such that $W_n(F_n) = 0$ and every complex root $z \in \mathbb{C}$ of $W_n$ satisfies $|z| \le q^{n/2}$.
--
--   This theorem eliminates the entire upper half of cohomology ($n < i < 2n$) and all non-middle Poincaré pairings $B_i$ ($1 \le i < n$). For $n < i < 2n$, setting $V'_i = V_{2n-i}^*$ with $F'_i = (q^n F_{2n-i}^{-1})^*$ canonically supplies the dual pairings, upper-half traces via $\operatorname{Tr}(g^*) = \operatorname{Tr}(g)$, and monic upper-half annihilating polynomials $\widetilde{W}_j(X) = q^{(n-j)\deg W_j} W_j(X / q^{n-j}) \in \mathbb{Z}[X]$.
-- source:
--   P. Deligne, La conjecture de Weil. I, Publ. Math. IHÉS 43 (1974), pp. 273–307 (lower-half ℓ-adic cohomology H^1, …, H^n over ℚ_ℓ via Poincaré duality)

import Mathlib
import Definitions.Def_WeilConjectures_projectiveSpace
import Definitions.Def_WeilConjectures_zetaFunction

open AlgebraicGeometry CategoryTheory Polynomial
open WeilConjectures

theorem WeilConjectures.exists_qladic_lower_half_cohomology_of_ge_two (p : ℕ) [Fact p.Prime]
    (k : Type) [Field k] [Finite k] [CharP k p] (n : ℕ) (hn : 2 ≤ n)
    (X : Scheme.{0}) (f : X ⟶ Spec (.of k))
    [SmoothOfRelativeDimension n f] [GeometricallyIrreducible f]
    (hproj : IsProjectiveOver k f)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓp : ℓ ≠ p) :
    ∃ (V : ℕ → Type) (_ : ∀ i, AddCommGroup (V i)) (_ : ∀ i, Module (Padic ℓ) (V i))
      (_ : ∀ i, Module.Finite (Padic ℓ) (V i))
      (F : ∀ i, V i ≃ₗ[Padic ℓ] V i)
      (Bmid : V n →ₗ[Padic ℓ] V n →ₗ[Padic ℓ] Padic ℓ),
      (∀ m : ℕ, 0 < m →
        (pointCount p f m : Padic ℓ) =
          1 + ((Nat.card k : Padic ℓ) ^ n) ^ m +
            (-1 : Padic ℓ) ^ n *
              LinearMap.trace (Padic ℓ) (V n) ((F n : V n →ₗ[Padic ℓ] V n) ^ m) +
            ∑ i ∈ Finset.Ico 1 n,
              (-1 : Padic ℓ) ^ i *
                (LinearMap.trace (Padic ℓ) (V i) ((F i : V i →ₗ[Padic ℓ] V i) ^ m) +
                 ((Nat.card k : Padic ℓ) ^ n) ^ m *
                   LinearMap.trace (Padic ℓ) (V i) (((F i).symm : V i →ₗ[Padic ℓ] V i) ^ m))) ∧
      (∀ x y : V n, Bmid (F n x) (F n y) = (Nat.card k : Padic ℓ) ^ n * Bmid x y) ∧
      ((∀ x : V n, (∀ y : V n, Bmid x y = 0) → x = 0) ∧
       (∀ y : V n, (∀ x : V n, Bmid x y = 0) → y = 0)) ∧
      (∀ i, 1 ≤ i → i < n → ∃ W : ℤ[X], W.Monic ∧ aeval (F i : V i →ₗ[Padic ℓ] V i) W = 0 ∧
        ∀ z : ℂ, aeval z W = 0 → ‖z‖ = (Nat.card k : ℝ) ^ ((i : ℝ) / 2)) ∧
      (∃ W : ℤ[X], W.Monic ∧ aeval (F n : V n →ₗ[Padic ℓ] V n) W = 0 ∧
        ∀ z : ℂ, aeval z W = 0 → ‖z‖ ≤ (Nat.card k : ℝ) ^ ((n : ℝ) / 2)) := by
  sorry
