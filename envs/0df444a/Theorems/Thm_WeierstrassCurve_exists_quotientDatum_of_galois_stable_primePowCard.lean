-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_quotientDatum_of_galois_stable_primePowCard
-- name    : WeierstrassCurve.exists_quotientDatum_of_galois_stable_primePowCard
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.985064+00:00
-- url     : https://prove2.me/theorems/72c05268-be08-573d-9068-b46536612d5f
-- title:
--   Quotient data for cyclic p^m-subgroups from the prime-level case
-- statement:
--   Let $W$ be a Weierstrass curve over $\mathbb{Z}$ with $\Delta_W \neq 0$ and let $p$ be a prime. Assume the prime-level quotient datum `hQD1`: for every Weierstrass curve $V$ over $\mathbb{Z}$ with $\Delta_V \neq 0$ and every subgroup $L$ of the group of points of $V$ base-changed to $\overline{\mathbb{Q}}$ with $\mathrm{card}\,L = p$ and stable under every $\sigma \in \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$, there are a Weierstrass curve $V'$ over $\mathbb{Z}$ with $\Delta_{V'} \neq 0$ and an additive map $\chi$ from the $\overline{\mathbb{Q}}$-points of $V$ to those of $V'$ with kernel exactly $L$, commuting with the Galois action, such that for every prime $q \neq p$ with $q \mid \Delta_V$ and $q \nmid c_4(V)$ one has $q \mid \Delta_{V'}$, $q \nmid c_4(V')$, and for every valuation subring $A$ of $\overline{\mathbb{Q}}$ with $q$ a non-unit of $A$ and every point $y$ of $V$: $\chi(y)$ satisfies `InZeroComponentAt` for $V'$ at $A$ if and only if $y - k$ satisfies `InZeroComponentAt` for $V$ at $A$ for some $k \in L$. Here `InZeroComponentAt` holds of a point $P$ when $P = 0$, or $P$ is an affine nonsingular point $(x,y)$ over $\overline{\mathbb{Q}}$ with either $x \notin A$, or $x, y \in A$ and the residues of $x$ and $y$ give a nonsingular point of the reduction of the curve over the residue field of $A$. Then, given $m \in \mathbb{N}$ and a subgroup $K$ of the $\overline{\mathbb{Q}}$-points of $W$ with $\mathrm{card}\,K = p^m$, $K$ additively cyclic, $p^m \cdot x = 0$ for all $x \in K$, and $K$ stable under every element of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$, the conclusion above holds verbatim with $W, K$ in place of $V, L$: there exist $W'$ over $\mathbb{Z}$ with $\Delta_{W'} \neq 0$ and a Galois-equivariant additive map $\varphi$ with kernel $K$ preserving, at every prime $q \neq p$ with $q \mid \Delta_W$, $q \nmid c_4(W)$, both the divisibility conditions and the transport law for zero components, with $K$ in place of $L$.
--
--   This is the inductive passage from the quotient of an elliptic curve by a Galois-stable subgroup of order $p$ to the quotient by a cyclic Galois-stable subgroup of order $p^m$, together with the transport of multiplicative reduction and of the identity component of the reduction at primes $q \neq p$. It feeds the study of Frey curves with large cyclic Galois-stable $p$-power subgroups, being used by [`FreyPackage.frey_no_cofixed_large`](thm.html#FreyPackage.frey_no_cofixed_large).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_quotientDatum_of_galois_stable_primePowCard.lean

import Mathlib
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_EllipticCurve_ZeroComponentAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point ValuationSubring

theorem WeierstrassCurve.exists_quotientDatum_of_galois_stable_primePowCard
    (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0)
    {p : ℕ} (hp : p.Prime)
    (hQD1 : ∀ (V : WeierstrassCurve ℤ), V.Δ ≠ 0 →
      ∀ (L : AddSubgroup ((V.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point),
        Nat.card L = p →
        (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ∀ x ∈ L, σ • x ∈ L) →
      ∃ (V' : WeierstrassCurve ℤ)
        (χ : ((V.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point →+
             ((V'.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point),
        V'.Δ ≠ 0 ∧ χ.ker = L ∧
        (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
           (x : ((V.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point),
          χ (σ • x) = σ • χ x) ∧
        (∀ q : ℕ, q.Prime → q ≠ p → (q : ℤ) ∣ V.Δ → ¬ (q : ℤ) ∣ V.c₄ →
          ((q : ℤ) ∣ V'.Δ ∧ ¬ (q : ℤ) ∣ V'.c₄ ∧
            ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime q →
              ∀ y : ((V.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point,
                (V'.InZeroComponentAt A (χ y) ↔
                  ∃ k ∈ L, V.InZeroComponentAt A (y - k)))))
    (m : ℕ)
    (K : AddSubgroup ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point)
    (hKcard : Nat.card K = p ^ m) (hK1 : IsAddCyclic K)
    (hKtors : ∀ x ∈ K, p ^ m • x = 0)
    (hKstab : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ∀ x ∈ K, σ • x ∈ K) :
    ∃ (W' : WeierstrassCurve ℤ)
      (φ : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point →+
           ((W'.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point),
      W'.Δ ≠ 0 ∧ φ.ker = K ∧
      (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
         (x : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point),
        φ (σ • x) = σ • φ x) ∧
      (∀ q : ℕ, q.Prime → q ≠ p → (q : ℤ) ∣ W.Δ → ¬ (q : ℤ) ∣ W.c₄ →
        ((q : ℤ) ∣ W'.Δ ∧ ¬ (q : ℤ) ∣ W'.c₄ ∧
          ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime q →
            ∀ y : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point,
              (W'.InZeroComponentAt A (φ y) ↔
                ∃ k ∈ K, W.InZeroComponentAt A (y - k)))) := by sorry
