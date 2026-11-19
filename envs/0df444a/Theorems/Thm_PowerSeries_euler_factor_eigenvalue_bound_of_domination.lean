-- Prove2me | Theorems.Thm_PowerSeries_euler_factor_eigenvalue_bound_of_domination
-- name    : PowerSeries.euler_factor_eigenvalue_bound_of_domination
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-18T16:52:55.665011+00:00
-- url     : https://prove2.me/theorems/9528e16d-d342-4ae6-83e8-840e434863a7
-- title:
--   Domination of one Euler factor: if L = exp(Σ N_m T^m/m) has coefficients O(n^J B^n) and a degree-d Euler factor contributes 0 ≤ c_m ≤ N_m, its inverse roots satisfy |α| ≤ B^d
-- statement:
--   Let $L(T) \in \mathbb C[[T]]$ be a power series and $(N_m)_{m \ge 1}$ real numbers with
--
--   $$L(0) = 1, \qquad L' = L \cdot \sum_{k \ge 0} N_{k+1} T^k ,$$
--
--   i.e. $L(T) = \exp\left(\sum_{m \ge 1} N_m T^m / m\right)$. Let $A$ be a finite multiset of complex numbers and $d \ge 1$ an integer, and put, for $m \ge 1$,
--
--   $$c_m = \begin{cases} d \sum_{\alpha \in A} \alpha^{m/d} & \text{if } d \mid m, \\ 0 & \text{otherwise,} \end{cases}$$
--
--   so that $\prod_{\alpha \in A} (1 - \alpha T^d)^{-1} = \exp\left(\sum_{m \ge 1} c_m T^m / m\right)$. Assume every $c_m$ is real with $0 \le c_m \le N_m$, and that the coefficients of $L$ grow at most like $B^n$ up to a polynomial factor: there are $B > 0$, $C \in \mathbb R$ and $J \in \mathbb N$ with $\left|[T^n]\, L\right| \le C\,(n+1)^J B^n$ for all $n \ge 0$. Then
--
--   $$|\alpha| \le B^d \qquad \text{for every } \alpha \in A .$$
--
--   Role: in Deligne's proof of the Riemann hypothesis over finite fields (Weil II), as presented by Katz, $L$ is the $L$-function of a lisse sheaf with real nonnegative point sums $N_m$ on a curve over $\mathbb F_q$, $A$ is the multiset of Frobenius eigenvalues at one closed point of degree $d$, and $c_m$ is that point's contribution to $N_m$. The statement says that a single Euler factor cannot have a pole closer to the origin than the radius of convergence $1/B$ of the whole $L$-function. Combined with the rationality of $L$ (Grothendieck-Lefschetz) and Rankin's squaring trick it bounds the weights of the sheaf at every closed point.
--
--   **Formalization Note**: `L : PowerSeries ℂ`, `N : ℕ → ℝ` (`N 0` plays no role) with `PowerSeries.constantCoeff L = 1` and `PowerSeries.derivative ℂ L = L * PowerSeries.mk (fun k => (N (k + 1) : ℂ))`, the logarithmic-derivative form of $L = \exp \sum_m N_m T^m/m$, which determines $L$ uniquely in characteristic $0$. The contribution is given as a real sequence `c : ℕ → ℝ` with `(if d ∣ m then (d : ℂ) * (A.map fun α => α ^ (m / d)).sum else 0) = (c m : ℂ)` for `m ≥ 1` (natural-number division `m / d` is exact when `d ∣ m`), together with `0 ≤ c m` and `c m ≤ N m`. The growth bound is `‖PowerSeries.coeff n L‖ ≤ C * ((n : ℝ) + 1) ^ J * B ^ n` and the conclusion is `∀ α ∈ A, ‖α‖ ≤ B ^ d`. The hypotheses are satisfiable: `A = {1}`, `d = 1`, `c = N = 1`, `L = PowerSeries.mk (fun _ => 1)` $= (1 - T)^{-1}$ and `B = C = 1`, `J = 0`, where the bound is sharp.
-- source:
--   N. M. Katz, L-functions and monodromy: four lectures on Weil II, Advances in Mathematics 160 (2001), 81-132 (domination of one Euler factor via the Positive Coefficient Lemma, pp. 24-25 of the lecture notes); P. Deligne, La conjecture de Weil. II, Publ. Math. IHES 52 (1980), 137-252

import Mathlib

set_option autoImplicit false

theorem PowerSeries.euler_factor_eigenvalue_bound_of_domination (L : PowerSeries ℂ) (N : ℕ → ℝ)
    (hL0 : PowerSeries.constantCoeff L = 1)
    (hL : PowerSeries.derivative ℂ L = L * PowerSeries.mk (fun k => (N (k + 1) : ℂ)))
    (A : Multiset ℂ) (d : ℕ) (hd : 0 < d) (c : ℕ → ℝ)
    (hcA : ∀ m : ℕ, 1 ≤ m →
      (if d ∣ m then (d : ℂ) * (A.map fun α => α ^ (m / d)).sum else 0) = (c m : ℂ))
    (hc : ∀ m : ℕ, 1 ≤ m → 0 ≤ c m) (hcN : ∀ m : ℕ, 1 ≤ m → c m ≤ N m)
    (B : ℝ) (hB : 0 < B) (C : ℝ) (J : ℕ)
    (hLg : ∀ n : ℕ, ‖PowerSeries.coeff n L‖ ≤ C * ((n : ℝ) + 1) ^ J * B ^ n) :
    ∀ α ∈ A, ‖α‖ ≤ B ^ d := by sorry
