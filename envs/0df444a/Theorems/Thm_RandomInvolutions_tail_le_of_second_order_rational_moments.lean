-- Prove2me | Theorems.Thm_RandomInvolutions_tail_le_of_second_order_rational_moments
-- name    : RandomInvolutions.tail_le_of_second_order_rational_moments
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-16T11:46:19.57243+00:00
-- url     : https://prove2.me/theorems/da74d656-576c-4176-b11d-2b196af4cfce
-- title:
--   The polynomial method at second order, uniformly along rays of fixed-point counts
-- statement:
--   An abstract tail bound, a second-order version of the polynomial method of Chen, Garza-Vargas, Tropp and van Handel that is uniform in a parameter $\kappa \in \mathbb N^r$. Let $E_{\kappa,N}$ be positive linear functionals on functions on $\mathbb R$, of mass at most $1$ on $[-K, K]$. Their moments are rational in $1/N$ with a common denominator: for each $q$ there is $g_q$ with $\deg g_q \le Cq$ and $1/2 \le g_q \le 1$ on $[0, 1/(Cq^2)]$, and for each polynomial $h$ of degree $\le q$ and each $\kappa$ there is $f$ with $\deg f \le Cq$ such that $E_{\kappa,N}(h) = f(1/N)/g_q(1/N)$ for every admissible $N \ge Cq$ (`AdmK N κ`). Suppose that along admissible $N \to \infty$
--   $$E_{\kappa,N}(x^p) = a_p + \frac{A_p + \sum_i \kappa_i B_{i,p}}{N} + \frac{C_{0,p} + \sum_i \kappa_i C_{1,i,p} + \sum_{i,j} \kappa_i \kappa_j C_{2,ij,p}}{N^2} + o(N^{-2}),$$
--   and that $a_p$, $A_p$, $B_{i,p}$ and $C_{2,ij,p}$ (but not $C_0$ or $C_1$) grow at most like $C_\delta(\rho + \delta)^p$ for every $\delta > 0$. Then for every $\varepsilon > 0$ there is $C$ with
--   $$E_{\kappa,N}\big(\mathbf 1_{\{|x| \ge \rho + \varepsilon\}}\big) \le C\,\frac{\ell(\kappa)}{N^2} + C\,\frac{\ell(\kappa)^3}{N^3}$$
--   for all $\kappa$ and all admissible $N \ge 1$, where $\ell(\kappa) = 1 + \sum_i \kappa_i$ (`lam`).
--
--   The first-order version, for a single ray, is `BordenaveCollins.exists_tail_le_of_rational_moments`.
-- source:
--   Chen, C.-F., Garza-Vargas, J., Tropp, J. A. and van Handel, R., A new approach to strong convergence, Ann. of Math. (2) 203 (2026) 555–602, https://doi.org/10.4007/annals.2026.203.2.4 (arXiv:2405.16026v3, whose page numbers are used), p. 20-23, 29-30, Theorems 6.1 and 7.1 and the proof of Theorem 3.9, at second order and uniformly along rays, in an abstract form

import Mathlib
import Definitions.Def_RandomInvolutions

open Filter Topology Polynomial

namespace RandomInvolutions

theorem tail_le_of_second_order_rational_moments (K : ℝ) (hK : 0 < K) (r : ℕ) (E : (Fin r → ℕ) → ℕ → (ℝ → ℝ) → ℝ)
    (hadd : ∀ κ N f g, E κ N (f + g) = E κ N f + E κ N g)
    (hsmul : ∀ κ N (a : ℝ) f, E κ N (a • f) = a * E κ N f)
    (hmono : ∀ κ N f g, (∀ x ∈ Set.Icc (-K) K, f x ≤ g x) → E κ N f ≤ E κ N g)
    (hone : ∀ κ N, E κ N (fun _ => 1) ≤ 1)
    (hrat : ∃ C : ℕ, 1 ≤ C ∧ ∀ q : ℕ, 1 ≤ q → ∃ gq : ℝ[X], gq.natDegree ≤ C * q ∧
      (∀ x ∈ Set.Icc (0 : ℝ) (1 / ((C : ℝ) * (q : ℝ) ^ 2)), 1 / 2 ≤ gq.eval x ∧ gq.eval x ≤ 1) ∧
      ∀ h : ℝ[X], h.natDegree ≤ q → ∀ κ : Fin r → ℕ, ∃ f : ℝ[X], f.natDegree ≤ C * q ∧
        ∀ N : ℕ, AdmK N κ → C * q ≤ N →
          E κ N (fun x => h.eval x) = f.eval (1 / (N : ℝ)) / gq.eval (1 / (N : ℝ)))
    (ρ : ℝ) (hρ : 0 ≤ ρ) (a A : ℕ → ℝ) (B : Fin r → ℕ → ℝ) (C2 : Fin r → Fin r → ℕ → ℝ)
    (hexp : ∃ (C0 : ℕ → ℝ) (C1 : Fin r → ℕ → ℝ), ∀ (κ : Fin r → ℕ) (p : ℕ),
      Tendsto (fun N : ℕ => (N : ℝ) ^ 2 * (E κ N (fun x => x ^ p) - a p -
          (A p + ∑ i, (κ i : ℝ) * B i p) / N)) (admF κ)
        (𝓝 (C0 p + ∑ i, (κ i : ℝ) * C1 i p + ∑ i, ∑ j, (κ i : ℝ) * κ j * C2 i j p)))
    (hagrow : ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, ∀ p : ℕ, |a p| ≤ C * (ρ + δ) ^ p)
    (hAgrow : ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, ∀ p : ℕ, |A p| ≤ C * (ρ + δ) ^ p)
    (hBgrow : ∀ i, ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, ∀ p : ℕ, |B i p| ≤ C * (ρ + δ) ^ p)
    (hC2grow : ∀ i j, ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, ∀ p : ℕ, |C2 i j p| ≤ C * (ρ + δ) ^ p)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ (κ : Fin r → ℕ) (N : ℕ), AdmK N κ → 1 ≤ N →
      E κ N (fun x => if ρ + ε ≤ |x| then 1 else 0) ≤
        C * lam κ / (N : ℝ) ^ 2 + C * lam κ ^ 3 / (N : ℝ) ^ 3 := by
  sorry

end RandomInvolutions
