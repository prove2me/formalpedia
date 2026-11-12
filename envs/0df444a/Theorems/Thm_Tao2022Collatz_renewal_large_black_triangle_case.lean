-- Prove2me | Theorems.Thm_Tao2022Collatz_renewal_large_black_triangle_case
-- name    : Tao2022Collatz.renewal_large_black_triangle_case
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-11T23:46:28.599607+00:00
-- url     : https://prove2.me/theorems/62e0f618-777a-4304-9a5c-a6657b9221b0
-- title:
--   Tao's renewal induction, Case 3: a large black triangle still yields the decay $V(r,j,l)\le M(r+1)^{-A}$
-- statement:
--   Let $0<\varepsilon<1/100$, $A>0$ and $0<\theta\le 1/2$. Write $\theta(J,L)$ for the representative $t\in[0,3^n)$ of $\xi\,3^{2J-2}\,2^{-(L-1)}\bmod 3^n$ and $N(J,L)\in(-3^n/2,3^n/2]$ for its least-absolute-value representative; $(J,L)$ is *white* if $\varepsilon 3^n<\theta(J,L)<(1-\varepsilon)3^n$ and *black* otherwise. Let $V$ satisfy $V(0,j,l)=1$ and $V(r+1,j,l)=\sum_{a_1,a_2\in[1,K]}2^{-(a_1+a_2)}e^{-\varepsilon^3\mathbf 1[a_1+a_2=3,\ (j+1,l+a_1+a_2)\text{ white}]}V(r,j+1,l+a_1+a_2)$ (Tao's first-step recursion (7.35) for the renewal expectation in (7.10), with $\mathrm{Geom}(2)$ variables truncated to $[1,K]$). Then there is $R_1$ such that for all $R_0\ge R_1$, $M\ge 1$, $n$, $K\ge 2$, $\xi$ with $3\nmid\xi$ and every such $V$: if $r\ge R_0$, $j+r=\lfloor n/2\rfloor$, the bound $V(r',j',l')\le M(r'+1)^{-A}$ holds for all $r'<r$ with $j'+r'=\lfloor n/2\rfloor$ (the induction hypothesis), the point $(j+1,l+3)$ is black, $2^\beta$ exactly divides $N(j+1,l+3)$, and $\theta r<\lfloor\beta/2\rfloor+3$, then $V(r,j,l)\le M(r+1)^{-A}$.
--
--   Role: this is Case 3 of Tao's proof of Proposition 7.8 (the black triangle at $(j+1,l+3)$ has size $\gg r$): Lemma 7.10 shows that the renewal walk leaves the triangle and then meets white points often enough, and (7.56) closes the induction. Cases 1-2 and the induction itself are the sibling child renewal_white_decay_of_black_triangle_case.
--
--   **Formalization Note**: the 2-adic size of the triangle is expressed through $\beta=v_2(N(j+1,l+3))$; the expectation is any solution $V$ of its first-step recursion, so no probability space is needed.
-- source:
--   Terence Tao, Almost all orbits of the Collatz map attain almost bounded values, Forum of Mathematics, Pi 10 (2022), e12; arXiv:1909.03562v7, Section 7.2, proof of Proposition 7.8, Case 3 (large black triangle), Lemma 7.10 and estimates (7.51)-(7.56). https://arxiv.org/abs/1909.03562

import Mathlib

namespace Tao2022Collatz

theorem renewal_large_black_triangle_case :
    ∀ ε : ℝ, 0 < ε → ε < 1 / 100 → ∀ A : ℝ, 0 < A → ∀ θ : ℝ, 0 < θ → θ ≤ 1 / 2 →
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
        V r j l ≤ M * ((r : ℝ) + 1) ^ (-A) := by sorry

end Tao2022Collatz
