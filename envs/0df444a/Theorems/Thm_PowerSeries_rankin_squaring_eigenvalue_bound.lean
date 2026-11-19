-- Prove2me | Theorems.Thm_PowerSeries_rankin_squaring_eigenvalue_bound
-- name    : PowerSeries.rankin_squaring_eigenvalue_bound
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-18T16:36:35.068181+00:00
-- url     : https://prove2.me/theorems/74a368a8-4bfd-4909-9603-2471ce063b9e
-- title:
--   Rankin squaring (Deligne, Weil II): if the L-series of the tensor powers M^(2a) grow like (K^a c)^n and dominate the Euler factor at a point of degree d, its Frobenius eigenvalues satisfy |α|² ≤ K^d
-- statement:
--   Let $A$ be a finite multiset of complex numbers, let $d \ge 1$ be an integer, and suppose the power sums of $A$ are real: for every $k \ge 1$,
--
--   $$\sum_{\alpha \in A} \alpha^k = s_k \in \mathbb R .$$
--
--   Let $K > 0$ and $c > 0$ be real numbers. Assume that for every integer $a \ge 1$ there are a power series $L_a(T) \in \mathbb C[[T]]$ and real numbers $N_{a,m}$ ($m \ge 1$) such that
--
--   1. $L_a(0) = 1$ and $L_a' = L_a \cdot \sum_{k \ge 0} N_{a,k+1} T^k$ (formal derivative), i.e. $L_a(T) = \exp\left(\sum_{m \ge 1} N_{a,m} T^m / m\right)$;
--   2. for every $m \ge 1$: $N_{a,m} \ge d\, s_{m/d}^{\,2a}$ if $d \mid m$, and $N_{a,m} \ge 0$ if $d \nmid m$;
--   3. there are constants $C \in \mathbb R$ and $J \in \mathbb N$ with $\left|[T^n]\, L_a\right| \le C\,(n+1)^J\,(K^a c)^n$ for all $n \ge 0$.
--
--   Then every $\alpha \in A$ satisfies
--
--   $$|\alpha|^2 \le K^d .$$
--
--   Role: this is the Rankin squaring step of Deligne's proof of the Riemann hypothesis over finite fields (Weil II), in Katz's presentation. $A$ is the multiset of eigenvalues of $\mathrm{Frob}_x$ on a lisse sheaf $M$ with real traces at a closed point $x$ of degree $d$ of a curve $U$ over $\mathbb F_q$, and $L_a = L(U, M^{\otimes 2a}, T)$. Its logarithmic coefficients are $N_{a,m} = \sum_{\deg y \mid m} \deg y \cdot \mathrm{Tr}(\mathrm{Frob}_y^{m/\deg y} \mid M)^{2a}$, a sum of nonnegative real terms whose term at $y = x$ is $d\, s_{m/d}^{\,2a}$ (hypothesis 2). By the Grothendieck-Lefschetz trace formula $L_a$ is rational with poles at the inverse eigenvalues of Frobenius on $H^2_c$, of absolute value at most $q^{aw+1}$, which gives hypothesis 3 with $K = q^w$ and $c = q$; the conclusion $|\alpha| \le q^{dw/2}$ says that $M$ has weights $\le w$ at $x$. Proof idea: by Katz's positive coefficient lemma the Euler factor $\prod_\beta (1 - \beta T^d)^{-1}$, $\beta$ running over the $2a$-fold products of elements of $A$, is dominated coefficientwise by $L_a$; comparing growth rates gives $|\alpha|^{2a} \le (K^a c)^d$ for every $a \ge 1$, and $a \to \infty$ gives $|\alpha|^2 \le K^d$.
--
--   **Formalization Note**: $A$ is `A : Multiset ℂ` and the real power sums are `s : ℕ → ℝ` with `(A.map fun z => z ^ k).sum = (s k : ℂ)` for `k ≥ 1`. For each `a ≥ 1` the hypothesis `hL` provides `L : PowerSeries ℂ` and `N : ℕ → ℝ` with `PowerSeries.constantCoeff L = 1` and `PowerSeries.derivative ℂ L = L * PowerSeries.mk (fun k => (N (k + 1) : ℂ))` (the logarithmic-derivative form of $L = \exp \sum_m N_m T^m/m$, which determines $L$ uniquely in characteristic $0$; `N 0` plays no role), the domination `(if d ∣ m then (d : ℝ) * s (m / d) ^ (2 * a) else 0) ≤ N m` for `m ≥ 1` (natural-number division `m / d` is exact when `d ∣ m`), and the growth bound `‖PowerSeries.coeff n L‖ ≤ C * ((n : ℝ) + 1) ^ J * (K ^ a * c) ^ n`. The conclusion is `∀ α ∈ A, ‖α‖ ^ 2 ≤ K ^ d`. The hypotheses are satisfiable: for `A = {1}`, `s = 1`, `d = 1`, `K = c = 1` take `L = PowerSeries.mk (fun _ => 1)` $= (1 - T)^{-1}$ and `N = 1` for every `a`, and the bound is sharp there.
-- source:
--   N. M. Katz, L-functions and monodromy: four lectures on Weil II, Advances in Mathematics 160 (2001), 81-132 (Rankin squaring and domination of one Euler factor, pp. 24-26 of the lecture notes); P. Deligne, La conjecture de Weil. II, Publ. Math. IHES 52 (1980), 137-252

import Mathlib

set_option autoImplicit false

theorem PowerSeries.rankin_squaring_eigenvalue_bound (A : Multiset ℂ) (s : ℕ → ℝ)
    (hs : ∀ k : ℕ, 1 ≤ k → (A.map fun z => z ^ k).sum = (s k : ℂ))
    (d : ℕ) (hd : 0 < d) (K c : ℝ) (hK : 0 < K) (hc : 0 < c)
    (hL : ∀ a : ℕ, 1 ≤ a → ∃ (L : PowerSeries ℂ) (N : ℕ → ℝ),
      PowerSeries.constantCoeff L = 1 ∧
      PowerSeries.derivative ℂ L = L * PowerSeries.mk (fun k => (N (k + 1) : ℂ)) ∧
      (∀ m : ℕ, 1 ≤ m → (if d ∣ m then (d : ℝ) * s (m / d) ^ (2 * a) else 0) ≤ N m) ∧
      ∃ (C : ℝ) (J : ℕ), ∀ n : ℕ,
        ‖PowerSeries.coeff n L‖ ≤ C * ((n : ℝ) + 1) ^ J * (K ^ a * c) ^ n) :
    ∀ α ∈ A, ‖α‖ ^ 2 ≤ K ^ d := by sorry
