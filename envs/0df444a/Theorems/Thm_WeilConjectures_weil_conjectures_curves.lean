-- Prove2me | Theorems.Thm_WeilConjectures_weil_conjectures_curves
-- name    : WeilConjectures.weil_conjectures_curves
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-12T15:02:34.10914+00:00
-- url     : https://prove2.me/theorems/e03db1bf-9bea-406e-b9e5-1dab71eb84d6
-- title:
--   Weil conjectures for curves (Weil)
-- statement:
--   Let $k=\mathbb F_q$ and let $X$ be a non-singular projective curve over $k$ (smooth of relative dimension $1$, geometrically irreducible, projective). Then there are integer polynomials $P_0,\dots,P_{2}\in\mathbb Z[T]$ and finite multisets $\{\alpha_{ij}\}_j$ of nonzero complex numbers with
--
--   $$Z(X,T)\cdot P_0(T)P_2(T)\cdots P_{2}(T)=P_1(T)P_3(T)\cdots P_{1}(T),$$
--
--   $P_0(T)=1-T$, $P_{2}(T)=1-qT$, and $P_i(T)=\prod_j(1-\alpha_{ij}T)$ in $\mathbb C[T]$ for $1\le i\le 1$;
--
--   **Functional equation:** with $E=\sum_{i=0}^{2}(-1)^i\deg P_i$ and $Z(T)=\prod_{i\text{ odd}}P_i(T)/\prod_{i\text{ even}}P_i(T)$, there is a sign $\varepsilon=\pm1$ such that
--
--   $$Z\big(q^{-1}t^{-1}\big)=\varepsilon\,q^{E/2}\,t^{E}\,Z(t)$$
--
--   for every complex $t\ne0$ at which both sides are defined; and for $1\le i\le 1$ the multiset $\{\alpha_{2-i,j}\}_j$ equals $\{q/\alpha_{i,j}\}_j$;
--
--   **Riemann hypothesis:** $|\alpha_{ij}|=q^{i/2}$ for all $1\le i\le 1$ and all $j$.
--
--   This is the case $n=1$ of the Weil conjectures, proved by Weil.
--
--
--   **Formalization Note** The finite field is a type `k` with `[Field k] [Finite k] [CharP k p]`, $q$ = `Nat.card k`; $\mathbb F_{q^m}$ is `FiniteField.Extension k p m`; $N_m$ counts $k$-morphisms $\operatorname{Spec}\mathbb F_{q^m}\to X$; $Z(X,T)$ is `zetaFunction p f`. Projectivity is a closed immersion into `projectiveSpace k N` over $k$.
-- source:
--   Wikipedia, "Weil conjectures", https://en.wikipedia.org/wiki/Weil_conjectures (PDF snapshot supplied by the proposer, 14 pp.), section "Background and history" ("The case of curves over finite fields was proved by Weil"), applied to the statement in section "Statement of the Weil conjectures", items 1–3 with $n=1$

import Mathlib
import Definitions.Def_WeilConjectures_projectiveSpace
import Definitions.Def_WeilConjectures_zetaFunction

open AlgebraicGeometry CategoryTheory Polynomial

namespace WeilConjectures

theorem weil_conjectures_curves (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Finite k] [CharP k p]
    (X : Scheme.{0}) (f : X ⟶ Spec (.of k))
    [SmoothOfRelativeDimension 1 f] [GeometricallyIrreducible f]
    (hproj : IsProjectiveOver k f) :
    ∃ (P : ℕ → ℤ[X]) (α : ℕ → Multiset ℂ),
      zetaFunction p f *
          (∏ i ∈ (Finset.range (2 * 1 + 1)).filter Even,
            ((P i).map (Int.castRingHom ℚ) : PowerSeries ℚ)) =
        ∏ i ∈ (Finset.range (2 * 1 + 1)).filter Odd,
            ((P i).map (Int.castRingHom ℚ) : PowerSeries ℚ) ∧
      P 0 = 1 - Polynomial.X ∧
      P (2 * 1) = 1 - C ((Nat.card k : ℤ) ^ 1) * Polynomial.X ∧
      (∀ i, 1 ≤ i → i ≤ 2 * 1 - 1 →
        (P i).map (Int.castRingHom ℂ) = ((α i).map fun a => 1 - C a * Polynomial.X).prod ∧
        ∀ a ∈ α i, a ≠ 0) ∧
      (∃ ε : ℂ, (ε = 1 ∨ ε = -1) ∧
        ∀ t : ℂ, t ≠ 0 →
          (∏ i ∈ (Finset.range (2 * 1 + 1)).filter Even, aeval t (P i)) ≠ 0 →
          (∏ i ∈ (Finset.range (2 * 1 + 1)).filter Even,
              aeval (((Nat.card k : ℂ) ^ 1 * t)⁻¹) (P i)) ≠ 0 →
          (∏ i ∈ (Finset.range (2 * 1 + 1)).filter Odd,
                aeval (((Nat.card k : ℂ) ^ 1 * t)⁻¹) (P i)) /
              (∏ i ∈ (Finset.range (2 * 1 + 1)).filter Even,
                aeval (((Nat.card k : ℂ) ^ 1 * t)⁻¹) (P i)) =
            ε * (((Nat.card k : ℝ) ^ ((1 : ℝ) *
                ((∑ i ∈ Finset.range (2 * 1 + 1), (-1 : ℤ) ^ i * ((P i).natDegree : ℤ) : ℤ) : ℝ)
                  / 2) : ℝ) : ℂ) *
              t ^ (∑ i ∈ Finset.range (2 * 1 + 1), (-1 : ℤ) ^ i * ((P i).natDegree : ℤ)) *
              ((∏ i ∈ (Finset.range (2 * 1 + 1)).filter Odd, aeval t (P i)) /
                (∏ i ∈ (Finset.range (2 * 1 + 1)).filter Even, aeval t (P i)))) ∧
      (∀ i, 1 ≤ i → i ≤ 2 * 1 - 1 →
        α (2 * 1 - i) = (α i).map fun a => (Nat.card k : ℂ) ^ 1 / a) ∧
      (∀ i, 1 ≤ i → i ≤ 2 * 1 - 1 → ∀ a ∈ α i,
        ‖a‖ = (Nat.card k : ℝ) ^ ((i : ℝ) / 2)) := by sorry

end WeilConjectures
