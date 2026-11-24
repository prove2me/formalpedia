-- Prove2me | Theorems.Thm_WeilConjectures_exists_qladic_lower_half_conj_dual_of_ge_two
-- name    : WeilConjectures.exists_qladic_lower_half_conj_dual_of_ge_two
-- status  : Open
-- author  : @pageman
-- created : 2026-11-23T23:59:40.890946+00:00
-- url     : https://prove2.me/theorems/2ab263a7-3411-43ac-a31a-85c9c493d80b
-- title:
--   Lower-Half $\mathbb{Q}_\ell$-Adic Cohomology with Conjugating Dual-Frobenius and Exact Purity ($1 \le i \le n$)
-- statement:
--   Let $p$ be a prime, $k$ a finite field of characteristic $p$ with cardinality $q = |k|$, $f : X \to \operatorname{Spec} k$ a smooth, projective, geometrically irreducible morphism of relative dimension $n \ge 2$, and $\ell \ne p$ a prime. Then there exist finite-dimensional $\mathbb{Q}_\ell$-vector spaces $V_i$ ($i \in \mathbb{N}$), $\mathbb{Q}_\ell$-linear Frobenius automorphisms $F_i : V_i \xrightarrow{\sim} V_i$, and a middle dual-Frobenius equivalence $e_{\mathrm{mid}} : V_n \xrightarrow{\sim} V_n^*$ satisfying:
--
--   1. **Lower-half Grothendieck–Lefschetz trace formula:** For every integer $m \ge 1$,
--   $$N_m(X) = 1 + q^{nm} + (-1)^n \operatorname{Tr}_{\mathbb{Q}_\ell}(F_n^m) + \sum_{i=1}^{n-1} (-1)^i \bigl(\operatorname{Tr}_{\mathbb{Q}_\ell}(F_i^m) + q^{nm} \operatorname{Tr}_{\mathbb{Q}_\ell}(F_i^{-m})\bigr).$$
--   2. **Conjugating dual-Frobenius intertwiner:** $e_{\mathrm{mid}} \circ F_n \circ e_{\mathrm{mid}}^{-1} = (q^n F_n^{-1})^*$ as endomorphisms of $V_n^*$ (equivalently $e_{\mathrm{mid}}.\mathrm{conj}(F_n) = (q^n F_n^{-1})^*$).
--   3. **Exact weight purity in every lower-half degree including the middle:** For every $1 \le i \le n$, there exists a monic integer polynomial $W_i \in \mathbb{Z}[X]$ such that $W_i(F_i) = 0$ and every complex root $z \in \mathbb{C}$ of $W_i$ satisfies $|z| = q^{i/2}$.
--
--   This theorem replaces evaluation-style dual equivariance $e_{\mathrm{mid}}(F_n x)(F_n y) = q^n e_{\mathrm{mid}}(x)(y)$ by the equivalent `LinearEquiv.conj` form, and upgrades the middle-degree Deligne bound $|z| \le q^{n/2}$ to exact purity $|z| = q^{n/2}$. Evaluation equivariance is recovered by applying the conjugating identity to $e_{\mathrm{mid}}(x)$ and substituting $y \mapsto F_n y$; the Deligne bound follows from exact purity by $|z| = q^{n/2} \Rightarrow |z| \le q^{n/2}$.
-- source:
--   P. Deligne, La conjecture de Weil. I, Publ. Math. IHÉS 43 (1974), pp. 273–307 (pure weight dual-Frobenius form of middle-degree Poincaré duality)

import Mathlib
import Definitions.Def_WeilConjectures_projectiveSpace
import Definitions.Def_WeilConjectures_zetaFunction

open AlgebraicGeometry CategoryTheory Polynomial
open WeilConjectures

/-- Lower-half $\mathbb{Q}_\ell$-adic cohomology with dual-Frobenius written as a
`LinearEquiv.conj` intertwiner, and with exact weight purity in every degree
$1 \le i \le n$ (including the middle degree). -/

theorem WeilConjectures.exists_qladic_lower_half_conj_dual_of_ge_two (p : ℕ) [Fact p.Prime]
    (k : Type) [Field k] [Finite k] [CharP k p] (n : ℕ) (hn : 2 ≤ n)
    (X : Scheme.{0}) (f : X ⟶ Spec (.of k))
    [SmoothOfRelativeDimension n f] [GeometricallyIrreducible f]
    (hproj : IsProjectiveOver k f)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓp : ℓ ≠ p) :
    ∃ (V : ℕ → Type) (_ : ∀ i, AddCommGroup (V i)) (_ : ∀ i, Module (Padic ℓ) (V i))
      (_ : ∀ i, Module.Finite (Padic ℓ) (V i))
      (F : ∀ i, V i ≃ₗ[Padic ℓ] V i)
      (eMid : V n ≃ₗ[Padic ℓ] Module.Dual (Padic ℓ) (V n)),
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
      (eMid.conj (F n : V n →ₗ[Padic ℓ] V n) =
        (((Nat.card k : Padic ℓ) ^ n) • ((F n).symm : V n →ₗ[Padic ℓ] V n)).dualMap) ∧
      (∀ i, 1 ≤ i → i ≤ n → ∃ W : ℤ[X], W.Monic ∧ aeval (F i : V i →ₗ[Padic ℓ] V i) W = 0 ∧
        ∀ z : ℂ, aeval z W = 0 → ‖z‖ = (Nat.card k : ℝ) ^ ((i : ℝ) / 2)) := by
  sorry
