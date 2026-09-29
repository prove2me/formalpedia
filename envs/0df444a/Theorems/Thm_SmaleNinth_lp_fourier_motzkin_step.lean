-- Prove2me | Theorems.Thm_SmaleNinth_lp_fourier_motzkin_step
-- name    : SmaleNinth.lp_fourier_motzkin_step
-- status  : Proved
-- author  : @Zexuan Liu
-- created : 2026-09-08T01:47:04.661772+00:00
-- url     : https://prove2.me/theorems/6820d283-bd2b-4686-89c2-a20fe9d80174
-- title:
--   Fourier-Motzkin elimination of one variable
-- statement:
--   Let $A \in \mathbb{R}^{m \times (n+1)}$ and $c \in \mathbb{R}^m$, and write $\beta_i = A_{i,n}$ for the coefficient of the last variable in row $i$ and $\alpha_i \in \mathbb{R}^n$ for the remaining coefficients. Then the system $Ax \ge c$ in $n+1$ variables has a solution if and only if the following system in the $n$ unknowns $y$ has one:
--
--   $$\alpha_i^{\mathsf T} y \ge c_i \quad (\beta_i = 0), \qquad (\beta_i \alpha_j - \beta_j \alpha_i)^{\mathsf T} y \ \ge\ \beta_i c_j - \beta_j c_i \quad (\beta_i > 0 > \beta_j).$$
--
--   This is one step of Fourier–Motzkin elimination. Necessity holds because each inequality of the reduced system is a nonnegative combination of two inequalities of the original one, chosen so that the last variable cancels: the pair inequality is $(-\beta_j)$ times row $i$ plus $\beta_i$ times row $j$. Sufficiency holds because a solution $y$ of the reduced system can be completed by any value $v$ of the last variable lying between the largest lower bound $\max_{\beta_i>0} (c_i - \alpha_i^{\mathsf T} y)/\beta_i$ and the smallest upper bound $\min_{\beta_j<0}(c_j - \alpha_j^{\mathsf T} y)/\beta_j$; the pair inequalities say precisely that every lower bound is at most every upper bound, and when one of the two families is empty any sufficiently extreme value works.
--
--   Iterating the step eliminates all variables and decides feasibility, which gives an elementary proof that linear feasibility over the reals is decidable, and, by tracking the nonnegative multipliers, the standard constructive route to Farkas' lemma and to linear programming duality. It also shows why the classical method is useless for the mission's goal: a single step can replace $m$ inequalities by roughly $m^2/4$, so eliminating $n$ variables in turn gives a bound that is doubly exponential in $n$, whereas Smale's ninth problem asks for a number of arithmetic operations polynomial in $m$ and $n$.
-- source:
--   J. B. J. Fourier (1826); T. Motzkin, Beitraege zur Theorie der linearen Ungleichungen, Dissertation, Basel 1936. See A. Schrijver, Theory of Linear and Integer Programming, Wiley 1986, Section 12.2, and Bertsimas-Tsitsiklis, Introduction to Linear Optimization, Athena Scientific 1997, Section 2.8.

import Definitions.Def_Polyhedron

/-!
Fourier-Motzkin elimination of one variable from a system of linear
inequalities in any number of variables: the induction step of the classical
elimination procedure.

Source: J. B. J. Fourier (1826) and T. Motzkin (1936); see A. Schrijver,
*Theory of Linear and Integer Programming*, Wiley 1986, Section 12.2
(Theorem 12.3 and the surrounding discussion), and Bertsimas-Tsitsiklis,
*Introduction to Linear Optimization*, Athena Scientific 1997, Section 2.8.
-/

open Matrix LinearOptimization

/-- **Fourier-Motzkin elimination of one variable.** The system `Ax >= c` in
`n+1` variables is feasible if and only if the system in `n` variables
obtained by eliminating the last one is feasible: the rows whose last
coefficient vanishes are kept, and each pair of rows with last coefficients of
opposite signs contributes the combination in which the last variable
cancels. -/

theorem SmaleNinth.lp_fourier_motzkin_step {m n : ℕ} (A : Matrix (Fin m) (Fin (n + 1)) ℝ)
    (c : Fin m → ℝ) :
    (polyhedron A c).Nonempty ↔
      ∃ y : Fin n → ℝ,
        (∀ i : Fin m, A i (Fin.last n) = 0 →
            c i ≤ ∑ k : Fin n, A i k.castSucc * y k) ∧
        (∀ i j : Fin m, 0 < A i (Fin.last n) → A j (Fin.last n) < 0 →
            A i (Fin.last n) * c j - A j (Fin.last n) * c i ≤
              ∑ k : Fin n, (A i (Fin.last n) * A j k.castSucc
                - A j (Fin.last n) * A i k.castSucc) * y k) := by sorry
