-- Prove2me | Theorems.Thm_Tao2022Collatz_renewal_white_decay_of_black_triangle_case
-- name    : Tao2022Collatz.renewal_white_decay_of_black_triangle_case
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-11T23:46:48.834118+00:00
-- url     : https://prove2.me/theorems/6b324bbb-3313-4788-9a8c-2e53065ab168
-- title:
--   Tao's renewal estimate (7.10) from its large-black-triangle case: Prop 7.8 induction, Cases 1 and 2
-- statement:
--   Assume the Case-3 statement renewal_large_black_triangle_case (the hypothesis of this implication: for $0<\varepsilon<1/100$, $A>0$, $0<\theta\le1/2$ a large black triangle at $(j+1,l+3)$ with $\theta r<\lfloor v_2(N)/2\rfloor+3$ preserves the bound $V(r,j,l)\le M(r+1)^{-A}$ given it for all $r'<r$). Then Tao's renewal estimate holds: for $0<\varepsilon<1/100$ and $A>0$ there is $C>0$ with $V(\lfloor n/2\rfloor,0,0)\le C n^{-A}$ for all $1\le n\le K$, $3\nmid\xi$ and every $V$ satisfying the first-step recursion. Write $\theta(J,L)$ for the representative $t\in[0,3^n)$ of $\xi\,3^{2J-2}\,2^{-(L-1)}\bmod 3^n$ and $N(J,L)\in(-3^n/2,3^n/2]$ for its least-absolute-value representative; $(J,L)$ is *white* if $\varepsilon 3^n<\theta(J,L)<(1-\varepsilon)3^n$ and *black* otherwise. Let $V$ satisfy $V(0,j,l)=1$ and $V(r+1,j,l)=\sum_{a_1,a_2\in[1,K]}2^{-(a_1+a_2)}e^{-\varepsilon^3\mathbf 1[a_1+a_2=3,\ (j+1,l+a_1+a_2)\text{ white}]}V(r,j+1,l+a_1+a_2)$ (Tao's first-step recursion (7.35) for the renewal expectation in (7.10), with $\mathrm{Geom}(2)$ variables truncated to $[1,K]$).
--
--   Role: this is the induction of Tao's Proposition 7.8 on $r$ (strong form of (7.10)), with Case 1 ($(j+1,l+3)$ white: one-step gain $e^{-\varepsilon^3}$) and Case 2 (small black triangle: the walk exits into a white point within a bounded number of steps, (7.51)) proved here, and Case 3 supplied by the hypothesis. Specialised to $r=\lfloor n/2\rfloor$, $j=l=0$ it is Proposition 7.3.
--
--   **Formalization Note**: as in the sibling, expectations are solutions $V$ of the recursion and the geometric variables are truncated to $[1,K]$, $K\ge n$.
-- source:
--   Terence Tao, Almost all orbits of the Collatz map attain almost bounded values, Forum of Mathematics, Pi 10 (2022), e12; arXiv:1909.03562v7, Section 7.2, Proposition 7.8 and its proof (Cases 1 and 2, (7.50)-(7.51)), giving Proposition 7.3 / (7.10). https://arxiv.org/abs/1909.03562

import Mathlib

namespace Tao2022Collatz

theorem renewal_white_decay_of_black_triangle_case :
    (∀ ε : ℝ, 0 < ε → ε < 1 / 100 → ∀ A : ℝ, 0 < A → ∀ θ : ℝ, 0 < θ → θ ≤ 1 / 2 →
      ∃ R1 : ℕ, ∀ R0 : ℕ, R1 ≤ R0 → ∀ M : ℝ, 1 ≤ M →
      ∀ n K : ℕ, ∀ ξ : ℤ, ¬ (3 : ℤ) ∣ ξ → 2 ≤ K → ∀ V : ℕ → ℕ → ℕ → ℝ,
        (∀ j l : ℕ, V 0 j l = 1) →
        (∀ r j l : ℕ, V (r + 1) j l =
          ∑ u ∈ Fintype.piFinset (fun _ : Fin 2 => Finset.Icc 1 K), ((1 : ℝ) / 2) ^ (∑ i, u i) *
            (if (∑ i, u i) = 3 ∧
                ε * 3 ^ n < ((((ξ : ZMod (3 ^ n)) * 9 ^ (j + 1 - 1) *
                  ((2 : ZMod (3 ^ n))⁻¹) ^ (l + ∑ i, u i - 1)).val : ℕ) : ℝ) ∧
                ((((ξ : ZMod (3 ^ n)) * 9 ^ (j + 1 - 1) *
                  ((2 : ZMod (3 ^ n))⁻¹) ^ (l + ∑ i, u i - 1)).val : ℕ) : ℝ) < (1 - ε) * 3 ^ n
              then Real.exp (-ε ^ 3) else 1) * V r (j + 1) (l + ∑ i, u i)) →
        ∀ r j l β : ℕ, R0 ≤ r → j + r = n / 2 →
        (∀ r' j' l' : ℕ, r' < r → j' + r' = n / 2 → V r' j' l' ≤ M * ((r' : ℝ) + 1) ^ (-A)) →
        ¬ (ε * 3 ^ n < ((((ξ : ZMod (3 ^ n)) * 9 ^ (j + 1 - 1) * ((2 : ZMod (3 ^ n))⁻¹) ^ (l + 3 - 1)).val : ℕ) : ℝ) ∧
            ((((ξ : ZMod (3 ^ n)) * 9 ^ (j + 1 - 1) * ((2 : ZMod (3 ^ n))⁻¹) ^ (l + 3 - 1)).val : ℕ) : ℝ) < (1 - ε) * 3 ^ n) →
        (2 : ℤ) ^ β ∣ ((ξ : ZMod (3 ^ n)) * 9 ^ (j + 1 - 1) * ((2 : ZMod (3 ^ n))⁻¹) ^ (l + 3 - 1)).valMinAbs →
        ¬ (2 : ℤ) ^ (β + 1) ∣ ((ξ : ZMod (3 ^ n)) * 9 ^ (j + 1 - 1) * ((2 : ZMod (3 ^ n))⁻¹) ^ (l + 3 - 1)).valMinAbs →
        θ * r < ((β / 2 + 3 : ℕ) : ℝ) →
        V r j l ≤ M * ((r : ℝ) + 1) ^ (-A)) →
    ∀ ε : ℝ, 0 < ε → ε < 1 / 100 → ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧
      ∀ n K : ℕ, 1 ≤ n → n ≤ K → ∀ ξ : ℤ, ¬ (3 : ℤ) ∣ ξ → ∀ V : ℕ → ℕ → ℕ → ℝ,
        (∀ j l : ℕ, V 0 j l = 1) →
        (∀ r j l : ℕ, V (r + 1) j l =
          ∑ u ∈ Fintype.piFinset (fun _ : Fin 2 => Finset.Icc 1 K), ((1 : ℝ) / 2) ^ (∑ i, u i) *
            (if (∑ i, u i) = 3 ∧
                ε * 3 ^ n < ((((ξ : ZMod (3 ^ n)) * 9 ^ (j + 1 - 1) *
                  ((2 : ZMod (3 ^ n))⁻¹) ^ (l + ∑ i, u i - 1)).val : ℕ) : ℝ) ∧
                ((((ξ : ZMod (3 ^ n)) * 9 ^ (j + 1 - 1) *
                  ((2 : ZMod (3 ^ n))⁻¹) ^ (l + ∑ i, u i - 1)).val : ℕ) : ℝ) < (1 - ε) * 3 ^ n
              then Real.exp (-ε ^ 3) else 1) * V r (j + 1) (l + ∑ i, u i)) →
        V (n / 2) 0 0 ≤ C * (n : ℝ) ^ (-A) := by sorry

end Tao2022Collatz
