-- Prove2me | Theorems.Thm_ShadowTomography_ClassicalLB_eq_1
-- name    : ShadowTomography.ClassicalLB.eq_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T17:07:39.99348+00:00
-- url     : https://prove2.me/theorems/ec1818c4-f7fa-4491-8977-234cf802bbad
-- title:
--   Equation (1): nearly independent half-size subsets
-- statement:
--   Choose $K=\lfloor c^N\rfloor$ subsets $S_1,\ldots,S_K\subseteq[N]$ independently and uniformly among subsets of size $N/2$. For some constant $1<c<2$, as even $N$ tends to infinity, the probability tends to one that every distinct pair satisfies
--
--   $$
--   \left|\,|S_i\cap S_j|-N/4\,\right|\le N/12.
--   $$
--
--   This supplies a family of measurements with controlled pairwise overlap for Theorem 16.
--
--   **Formalization Note** The probability is the ratio of the number of good families to the number of all half-size families. The printed overlap threshold $N/12$ is recorded exactly; the subsequent $\varepsilon/2$ display in the paper needs the stronger threshold $N/24$.
-- source:
--   Aaronson, Shadow Tomography of Quantum States, arXiv:1711.01053v2, p. 20, proof of Theorem 16, Eq. (1) and preceding probability claim

import Mathlib

namespace ShadowTomography.ClassicalLB

/-- Equation (1), including the preceding probability `1-o(1)` statement, as the
proportion of independent uniformly chosen half-size subset families. -/
theorem eq_1 :
    ∃ c : ℝ, 1 < c ∧ c < 2 ∧
      ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N →
        let K := Nat.floor (c ^ N)
        let half : Finset (Fin K → Finset (Fin N)) :=
          Finset.univ.filter (fun S => ∀ i, 2 * (S i).card = N)
        let good : Finset (Fin K → Finset (Fin N)) :=
          half.filter (fun S => ∀ i j, i ≠ j →
            |(((S i ∩ S j).card : ℝ) - (N : ℝ) / 4)| ≤ (N : ℝ) / 12)
        1 - η ≤ (good.card : ℝ) / (half.card : ℝ) := by sorry

end ShadowTomography.ClassicalLB
