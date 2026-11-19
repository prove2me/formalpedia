-- Prove2me | Theorems.Thm_PowerSeries_katz_positive_coefficient_lemma
-- name    : PowerSeries.katz_positive_coefficient_lemma
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-18T15:34:42.604424+00:00
-- url     : https://prove2.me/theorems/38446f51-2b87-49bb-8b0a-af2f7027a510
-- title:
--   Katz's positive coefficient lemma: if $Y'=YA$, $Z'=ZB$, $Y(0)=Z(0)=1$ and $0\le B\le A$ coefficientwise, then $0\le Z\le Y$ coefficientwise
-- statement:
--   Let $Y, Z, A, B \in \mathbb R[[T]]$ be formal power series with real coefficients, write $A = \sum_{j\ge0} a_j T^j$ and $B = \sum_{j\ge0} b_j T^j$, and let $'$ denote the formal derivative $d/dT$. Assume
--
--   $$Y(0) = Z(0) = 1, \qquad Y' = Y\,A, \qquad Z' = Z\,B, \qquad 0 \le b_j \le a_j \quad (j \ge 0).$$
--
--   Then for every $n \ge 0$ the coefficients of $T^n$ satisfy
--
--   $$0 \;\le\; [T^n]\,Z \;\le\; [T^n]\,Y.$$
--
--   Equivalently, in exponential form (Katz's Positive Coefficient Lemma): if $F = \sum_{m\ge1} f_m T^m/m$ and $G = \sum_{m\ge1} g_m T^m/m$ are real power series with $0 \le g_m \le f_m$ for all $m \ge 1$, then $\exp(G)$ has nonnegative coefficients and $\exp(F) - \exp(G)$ has nonnegative coefficients. Indeed $Y = \exp(F)$ is the unique series with $Y(0) = 1$ and $Y' = Y F'$, and $F' = \sum_{m\ge1} f_m T^{m-1}$, so the coefficients of $A = F'$ are the $f_m$. Taking $Z = 1$ and $B = 0$ gives the first half on its own: if $A$ has nonnegative coefficients then so has $Y$.
--
--   Role: in Deligne's proof of the Riemann hypothesis over finite fields (Weil II), as presented by Katz, the lemma is applied to $L$-functions $L(T) = \exp\left(\sum_m N_m T^m/m\right)$ whose logarithmic coefficients $N_m$ are nonnegative real numbers (traces of Frobenius on even tensor powers of a sheaf with real traces, Rankin's squaring trick). Every Euler factor of such an $L$-function is then dominated coefficientwise by the whole $L$-function, so the radius of convergence of $L(T)$ bounds the Frobenius eigenvalues at each closed point.
--
--   **Formalization Note**: power series are `PowerSeries ℝ`; `PowerSeries.derivative ℝ` is the formal derivative, `PowerSeries.constantCoeff` the constant term and `PowerSeries.coeff n` the coefficient of $T^n$. The exponential form is stated through the logarithmic derivative ($Y(0) = 1$, $Y' = YA$), which determines $Y = \exp\left(\int A\right)$ uniquely over a field of characteristic $0$. The conclusion contains both halves of the lemma: $0 \le Z$ is the nonnegativity statement for $Z = \exp(G)$ and $Z \le Y$ is the comparison. Example: $Y = \exp(T)$ (`PowerSeries.exp ℝ`) with $A = 1$, and $Z = 1$ with $B = 0$, satisfy all hypotheses.
-- source:
--   N. M. Katz, L-functions and monodromy: four lectures on Weil II, Advances in Mathematics 160 (2001), 81-132, Positive Coefficient Lemma (p. 24 of the lecture notes); P. Deligne, La conjecture de Weil. II, Publ. Math. IHES 52 (1980), 137-252 (the Rankin squaring argument)

import Mathlib

set_option autoImplicit false

theorem PowerSeries.katz_positive_coefficient_lemma (Y Z A B : PowerSeries ℝ)
    (hY0 : PowerSeries.constantCoeff Y = 1) (hZ0 : PowerSeries.constantCoeff Z = 1)
    (hY : PowerSeries.derivative ℝ Y = Y * A) (hZ : PowerSeries.derivative ℝ Z = Z * B)
    (hB : ∀ j : ℕ, 0 ≤ PowerSeries.coeff j B)
    (hBA : ∀ j : ℕ, PowerSeries.coeff j B ≤ PowerSeries.coeff j A) (n : ℕ) :
    0 ≤ PowerSeries.coeff n Z ∧ PowerSeries.coeff n Z ≤ PowerSeries.coeff n Y := by sorry
