-- Prove2me | Theorems.Thm_WeilConjectures_zetaOfCounts_mul_prod_charpolyRev_of_trace_formula
-- name    : WeilConjectures.zetaOfCounts_mul_prod_charpolyRev_of_trace_formula
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-21T23:44:14.225266+00:00
-- url     : https://prove2.me/theorems/82c00161-c2d5-4d79-90b7-c5404fb43806
-- title:
--   A trace formula gives the cohomological expression of the zeta series: $Z\cdot\prod_{i\ \mathrm{even}}\det(1-T\Phi_i)=\prod_{i\ \mathrm{odd}}\det(1-T\Phi_i)$
-- statement:
--   Let $K$ be a field of characteristic zero, let $s$ be a finite set of natural numbers and, for every $i$, let $\Phi_i$ be a square matrix over $K$ of size $d_i$. Let $(N_m)_{m\ge1}$ be a sequence of natural numbers that satisfies the trace formula
--
--   $$
--   N_m=\sum_{i\in s}(-1)^i\operatorname{tr}\big(\Phi_i^{\,m}\big)\qquad\text{in }K,\ \text{for all }m\ge1,
--   $$
--
--   and let
--
--   $$
--   Z(T)=\exp\Big(\sum_{m\ge1}\frac{N_m}{m}\,T^m\Big)\in\mathbb{Q}[[T]].
--   $$
--
--   Then, in $K[[T]]$,
--
--   $$
--   Z(T)\cdot\prod_{\substack{i\in s\\ i\ \mathrm{even}}}\det(1-T\Phi_i)=\prod_{\substack{i\in s\\ i\ \mathrm{odd}}}\det(1-T\Phi_i).
--   $$
--
--   Equivalently, $Z(T)=\prod_{i\in s}\det(1-T\Phi_i)^{(-1)^{i+1}}$. It rests on the identity $\exp\big(\sum_{m\ge1}\operatorname{tr}(\Phi^m)T^m/m\big)=\det(1-T\Phi)^{-1}$.
--
--   This is the formal step from a Lefschetz trace formula for Frobenius to the rationality of the zeta function: if $N_m$ is the number of $\mathbb{F}_{q^m}$-points of a variety and $\Phi_i$ is the matrix of Frobenius on its $i$-th cohomology group, the statement expresses $Z$ as the alternating product of the polynomials $P_i(T)=\det(1-T\Phi_i)$.
--
--   **Formalization Note** $Z$ is the platform's `zetaOfCounts N` (the value $N_0$ is ignored), viewed in $K[[T]]$ through `PowerSeries.map (algebraMap ℚ K)`. The polynomial $\det(1-T\Phi_i)$ is Mathlib's `Matrix.charpolyRev (Φ i)`, coerced to a power series. The index set `s` is an arbitrary finite set of natural numbers; for a variety of dimension $n$ it is $\{0,\dots,2n\}$.
-- source:
--   Wikipedia, *Weil conjectures*, https://en.wikipedia.org/wiki/Weil_conjectures, sections "Weil cohomology" and "Grothendieck's proofs of three of the four conjectures" (the Lefschetz fixed-point formula applied to Frobenius gives $\zeta$ as the alternating product of the $P_i=\det(I-TF\mid H^i)$, and rationality follows); P. Deligne, *La conjecture de Weil. I*, Publ. Math. IHÉS 43 (1974), 273–307, https://www.numdam.org/item/PMIHES_1974__43__273_0/, §1, (1.5.1)–(1.5.4): the identity $t\frac{d}{dt}\log\det(1-Ft,V)^{-1}=\sum_{n>0}\operatorname{Tr}(F^n,V)t^n$ is (1.5.3) and the resulting expression of $Z$ is (1.5.4); R. Hartshorne, *Algebraic Geometry*, Graduate Texts in Mathematics 52, Springer (1977), Appendix C, §4 (rationality from the Lefschetz fixed-point formula).

import Mathlib
import Definitions.Def_WeilConjectures_zetaFunction

open WeilConjectures

theorem WeilConjectures.zetaOfCounts_mul_prod_charpolyRev_of_trace_formula {K : Type*} [Field K]
    [CharZero K] (N : ℕ → ℕ) (s : Finset ℕ) (d : ℕ → ℕ)
    (Φ : (i : ℕ) → Matrix (Fin (d i)) (Fin (d i)) K)
    (htr : ∀ m : ℕ, 0 < m → (N m : K) = ∑ i ∈ s, (-1 : K) ^ i * ((Φ i) ^ m).trace) :
    PowerSeries.map (algebraMap ℚ K) (zetaOfCounts N) *
        ∏ i ∈ s.filter Even, (((Φ i).charpolyRev : Polynomial K) : PowerSeries K) =
      ∏ i ∈ s.filter Odd, (((Φ i).charpolyRev : Polynomial K) : PowerSeries K) := by sorry
