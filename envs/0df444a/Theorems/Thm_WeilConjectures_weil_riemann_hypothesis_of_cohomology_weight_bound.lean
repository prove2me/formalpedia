-- Prove2me | Theorems.Thm_WeilConjectures_weil_riemann_hypothesis_of_cohomology_weight_bound
-- name    : WeilConjectures.weil_riemann_hypothesis_of_cohomology_weight_bound
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T07:41:20.077711+00:00
-- url     : https://prove2.me/theorems/881b4eff-1178-4f11-956f-0a3c2e2cf87f
-- title:
--   The Weil factorization with the Riemann hypothesis from a trace formula, Poincaré duality and upper bounds on Frobenius eigenvalues
-- statement:
--   Let $n\ge0$ and $q\ge2$ be natural numbers and let $K$ be a field of characteristic zero. For $0\le i\le2n$ let $\Phi_i$ be a square matrix over $K$ of size $d_i$ (the matrix of an endomorphism $F_i$ of a $K$-vector space $H^i$ of dimension $d_i$), and let $(N_m)_{m\ge1}$ be natural numbers. Assume:
--
--   1. **Trace formula.** $N_m=\sum_{i=0}^{2n}(-1)^i\operatorname{tr}(\Phi_i^{\,m})$ in $K$ for all $m\ge1$.
--   2. **Poincaré duality.** For every $0\le i\le2n$ there is a perfect pairing $H^i\times H^{2n-i}\to K$ with $\langle F_ix,F_{2n-i}y\rangle=q^n\langle x,y\rangle$; in matrices, an invertible $G$ with $\Phi_i^{\mathsf T}\,G\,\Phi_{2n-i}=q^n\,G$.
--   3. **$H^0$.** $d_0=1$ and $\Phi_0=1$.
--   4. **Upper bound on the weights.** For every $0\le i\le2n$ there is a nonzero $W_i\in\mathbb{Q}[T]$ such that the characteristic polynomial $\det(T-\Phi_i)$ divides $W_i$ in $K[T]$, and every complex root $z$ of $W_i$ satisfies
--   $$
--   |z|\le q^{i/2}.
--   $$
--   In other words, every eigenvalue of $F_i$ is algebraic over $\mathbb{Q}$ and all its complex conjugates have absolute value at most $q^{i/2}$.
--
--   Let $Z(T)=\exp\big(\sum_{m\ge1}N_mT^m/m\big)\in\mathbb{Q}[[T]]$, and let $A,B\in\mathbb{Z}[T]$ be coprime in $\mathbb{Q}[T]$ with $A(0)=B(0)=1$ and $Z\cdot B=A$.
--
--   **Theorem.** There are polynomials $P_0,\dots,P_{2n}\in\mathbb{Z}[T]$ and finite multisets $\alpha_i$ of nonzero complex numbers such that
--
--   $$
--   Z(T)\cdot P_0(T)P_2(T)\cdots P_{2n}(T)=P_1(T)P_3(T)\cdots P_{2n-1}(T),
--   $$
--
--   $P_0(T)=1-T$, $P_{2n}(T)=1-q^nT$, $P_i(T)=\prod_{a\in\alpha_i}(1-aT)$ in $\mathbb{C}[T]$ for $1\le i\le2n-1$, and
--
--   $$
--   |a|=q^{i/2}\qquad\text{for all }a\in\alpha_i,\ 1\le i\le2n-1 .
--   $$
--
--   In fact $P_i(T)=\det(1-T\Phi_i)$: the statement includes that these polynomials have integer coefficients.
--
--   This is the formal part of the deduction of the Riemann hypothesis for varieties over finite fields from Deligne's estimate. Poincaré duality turns the upper bound $|\alpha|\le q^{i/2}$ on $H^i$ and on $H^{2n-i}$ into the equality $|\alpha|=q^{i/2}$; the weights then separate the factors $\det(1-TF_i)$ of the zeta function, which forces them to have rational, hence integral, coefficients. It involves no geometry; $N_m$ is an arbitrary sequence.
--
--   **Formalization Note** $Z$ is the platform's `zetaOfCounts N`; the conclusion has exactly the shape of the conclusion of `WeilConjectures.riemann_hypothesis`, with $q$ in place of `Nat.card k`. The matrices `Φ i` are indexed by all natural numbers $i$, but only $i\le2n$ is used. The pairing is given by its Gram matrix `G` with an explicit inverse `H`. "Complex root of $W$" is `aeval z W = 0` for `z : ℂ`, and $q^{i/2}$ is the real power `(q : ℝ) ^ ((i : ℝ) / 2)`. The hypothesis $q\ge2$ is `1 < q`; it is needed to separate the weights.
-- source:
--   Wikipedia, *Weil conjectures*, https://en.wikipedia.org/wiki/Weil_conjectures, section "Deligne's first proof of the Riemann hypothesis conjecture" (the conjectures depend on $|\alpha|=q^{i/2}$ for the eigenvalues of Frobenius on $H^i$; after the upper bound, "Poincaré duality then implies" the equality); P. Deligne, *La conjecture de Weil. I*, Publ. Math. IHÉS 43 (1974), 273–307, https://www.numdam.org/item/PMIHES_1974__43__273_0/, §1, Théorème (1.6), Lemme (1.7) and the proof of (1.7) ⇒ (1.6) (the $P_i=\det(1-F^*t,H^i)$ are pairwise coprime by the weights, so $P=\prod_{i\ \mathrm{impair}}P_i$, $Q=\prod_{i\ \mathrm{pair}}P_i$, and each $P_i$ has rational, hence integer, coefficients), and §2, (2.4) (the eigenvalues on $H^{2n-i}$ are the $q^n\alpha_j^{-1}$); R. Hartshorne, *Algebraic Geometry*, Graduate Texts in Mathematics 52, Springer (1977), Appendix C, §4.

import Mathlib
import Definitions.Def_WeilConjectures_zetaFunction

open Polynomial
open WeilConjectures

theorem WeilConjectures.weil_riemann_hypothesis_of_cohomology_weight_bound
    (N : ℕ → ℕ) (n q : ℕ) (hq : 1 < q) {K : Type*} [Field K] [CharZero K] (d : ℕ → ℕ)
    (Φ : (i : ℕ) → Matrix (Fin (d i)) (Fin (d i)) K)
    (htr : ∀ m : ℕ, 0 < m →
      (N m : K) = ∑ i ∈ Finset.range (2 * n + 1), (-1 : K) ^ i * ((Φ i) ^ m).trace)
    (hPD : ∀ i ≤ 2 * n, ∃ (G : Matrix (Fin (d i)) (Fin (d (2 * n - i))) K)
        (H : Matrix (Fin (d (2 * n - i))) (Fin (d i)) K),
        G * H = 1 ∧ H * G = 1 ∧ (Φ i).transpose * G * Φ (2 * n - i) = (q : K) ^ n • G)
    (hd0 : d 0 = 1) (hΦ0 : Φ 0 = 1)
    (hW : ∀ i ≤ 2 * n, ∃ W : ℚ[X], W ≠ 0 ∧ (Φ i).charpoly ∣ W.map (algebraMap ℚ K) ∧
        ∀ z : ℂ, aeval z W = 0 → ‖z‖ ≤ (q : ℝ) ^ ((i : ℝ) / 2))
    (A B : ℤ[X]) (hA : A.coeff 0 = 1) (hB : B.coeff 0 = 1)
    (hcop : IsCoprime (A.map (Int.castRingHom ℚ)) (B.map (Int.castRingHom ℚ)))
    (hZ : zetaOfCounts N * ((B.map (Int.castRingHom ℚ) : ℚ[X]) : PowerSeries ℚ) =
      ((A.map (Int.castRingHom ℚ) : ℚ[X]) : PowerSeries ℚ)) :
    ∃ (P : ℕ → ℤ[X]) (α : ℕ → Multiset ℂ),
      zetaOfCounts N *
          (∏ i ∈ (Finset.range (2 * n + 1)).filter Even,
            ((P i).map (Int.castRingHom ℚ) : PowerSeries ℚ)) =
        ∏ i ∈ (Finset.range (2 * n + 1)).filter Odd,
            ((P i).map (Int.castRingHom ℚ) : PowerSeries ℚ) ∧
      P 0 = 1 - Polynomial.X ∧
      P (2 * n) = 1 - C ((q : ℤ) ^ n) * Polynomial.X ∧
      (∀ i, 1 ≤ i → i ≤ 2 * n - 1 →
        (P i).map (Int.castRingHom ℂ) = ((α i).map fun a => 1 - C a * Polynomial.X).prod ∧
        ∀ a ∈ α i, a ≠ 0) ∧
      (∀ i, 1 ≤ i → i ≤ 2 * n - 1 → ∀ a ∈ α i,
        ‖a‖ = (q : ℝ) ^ ((i : ℝ) / 2)) := by sorry
