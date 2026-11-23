-- Prove2me | Theorems.Thm_WeilConjectures_exists_deligne_fg_pid_cohomology_of_ge_two
-- name    : WeilConjectures.exists_deligne_fg_pid_cohomology_of_ge_two
-- status  : Open
-- author  : @pageman
-- created : 2026-11-23T21:08:42.643807+00:00
-- url     : https://prove2.me/theorems/53c69651-2c8c-4f98-a840-03cea13e641f
-- title:
--   Finitely Generated Integral PID Weil Cohomology (Torsion Allowed) with Polynomial Weight Annihilation ($n \ge 2$)
-- statement:
--   Let $p$ be a prime, $k$ a finite field of characteristic $p$ with cardinality $q = |k|$, and $f : X \to \operatorname{Spec} k$ a smooth, projective, geometrically irreducible morphism of relative dimension $n \ge 2$. Then there exist a characteristic-zero principal ideal domain $R$, finitely generated $R$-modules $M_i$ ($i \in \mathbb{N}$, torsion permitted), $R$-linear Frobenius endomorphisms $F_i : M_i \to M_i$, lower-half cup-product pairings $\cup_i : M_i \times M_{2n-i} \to M_{2n}$ ($0 \le i \le n$), and a top-degree trace functional $\operatorname{tr} : M_{2n} \to R$ satisfying:
--
--   1. **Rational Grothendieck–Lefschetz trace formula:** Setting $K = \operatorname{Frac}(R)$, for every integer $m \ge 1$,
--   $$N_m(X) = \sum_{i=0}^{2n} (-1)^i \operatorname{Tr}_K((F_i \otimes_R K)^m).$$
--   2. **Frobenius-equivariant cup-trace duality modulo torsion:** For all $z \in M_{2n}$, $\operatorname{tr}(F_{2n}(z)) = q^n \operatorname{tr}(z)$; for all $0 \le i \le n$, $\cup_i(F_i x, F_{2n-i} y) = F_{2n}(\cup_i(x, y))$; and the left and right radicals of $(x, y) \mapsto \operatorname{tr}(\cup_i(x, y))$ consist solely of $R$-torsion elements.
--   3. **Connectedness in degree $0$ modulo torsion:** $\operatorname{rank}_R M_0 = 1$ and $F_0(x) - x$ is $R$-torsion for all $x \in M_0$.
--   4. **Deligne upper weight bound by polynomial annihilation modulo torsion:** For every $0 \le i \le 2n$, there exists a nonzero integer polynomial $W_i \in \mathbb{Z}[X]$ whose complex roots satisfy $|z| \le q^{i/2}$ such that $W_i(F_i)(x)$ is $R$-torsion for all $x \in M_i$.
--
--   This theorem models raw integral cohomology (such as $H^i_{\mathrm{\acute{e}t}}(X_{\bar k}, \mathbb{Z}_\ell)$ or crystalline cohomology $H^i_{\mathrm{cris}}(X/W(k))$) with arbitrary torsion allowed and requires only polynomial annihilation modulo torsion rather than explicit characteristic-polynomial divisibility. Quotienting by $R$-torsion and lifting annihilating polynomials via the algebraic closure recovers the free integral PID Weil cohomology leaf.
-- source:
--   P. Deligne, La conjecture de Weil. I, Publ. Math. IHÉS 43 (1974), pp. 273–307 (raw integral ℓ-adic cohomology with torsion, cup-trace duality modulo torsion, and weight-bounded polynomial annihilation)

import Mathlib
import Definitions.Def_WeilConjectures_projectiveSpace
import Definitions.Def_WeilConjectures_zetaFunction

open AlgebraicGeometry CategoryTheory Polynomial
open scoped TensorProduct
open WeilConjectures

theorem WeilConjectures.exists_deligne_fg_pid_cohomology_of_ge_two (p : ℕ) [Fact p.Prime]
    (k : Type) [Field k] [Finite k] [CharP k p] (n : ℕ) (hn : 2 ≤ n)
    (X : Scheme.{0}) (f : X ⟶ Spec (.of k))
    [SmoothOfRelativeDimension n f] [GeometricallyIrreducible f]
    (hproj : IsProjectiveOver k f) :
    ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : IsPrincipalIdealRing R) (_ : CharZero R)
      (M : ℕ → Type) (_ : ∀ i, AddCommGroup (M i)) (_ : ∀ i, Module R (M i))
      (_ : ∀ i, Module.Finite R (M i))
      (F : ∀ i, M i →ₗ[R] M i)
      (cup : ∀ i, i ≤ n → M i →ₗ[R] M (2 * n - i) →ₗ[R] M (2 * n))
      (tr : M (2 * n) →ₗ[R] R),
      (∀ m : ℕ, 0 < m →
        (pointCount p f m : FractionRing R) =
          ∑ i ∈ Finset.range (2 * n + 1),
            (-1 : FractionRing R) ^ i *
              LinearMap.trace (FractionRing R) (FractionRing R ⊗[R] M i)
                (((F i).baseChange (FractionRing R)) ^ m)) ∧
      (∀ z : M (2 * n), tr (F (2 * n) z) = (Nat.card k : R) ^ n * tr z) ∧
      (∀ i (hi : i ≤ n) (x : M i) (y : M (2 * n - i)),
        cup i hi (F i x) (F (2 * n - i) y) = F (2 * n) (cup i hi x y)) ∧
      (∀ i (hi : i ≤ n),
        (∀ x : M i, (∀ y : M (2 * n - i), tr (cup i hi x y) = 0) →
          ∃ r : R, r ≠ 0 ∧ r • x = 0) ∧
        (∀ y : M (2 * n - i), (∀ x : M i, tr (cup i hi x y) = 0) →
          ∃ r : R, r ≠ 0 ∧ r • y = 0)) ∧
      Module.finrank R (M 0) = 1 ∧
      (∀ x : M 0, ∃ r : R, r ≠ 0 ∧ r • (F 0 x - x) = 0) ∧
      (∀ i ≤ 2 * n, ∃ W : ℤ[X], W ≠ 0 ∧
        (∀ x : M i, ∃ r : R, r ≠ 0 ∧ r • (aeval (F i) W x) = 0) ∧
        ∀ z : ℂ, aeval z W = 0 → ‖z‖ ≤ (Nat.card k : ℝ) ^ ((i : ℝ) / 2)) := by
  sorry
