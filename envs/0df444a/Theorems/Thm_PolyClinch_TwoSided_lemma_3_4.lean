-- Prove2me | Theorems.Thm_PolyClinch_TwoSided_lemma_3_4
-- name    : PolyClinch.TwoSided.lemma_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:20:26.148539+00:00
-- url     : https://prove2.me/theorems/97c3302e-e475-4c1b-abb2-1df0f0df63df
-- title:
--   Lemma 3.4, p. 11 — for the output (y, π) of Algorithm 1 there is a revenue vector r with (17) and (18)
-- statement:
--   Let $\mathcal I$ be valid public information and $\varepsilon>0$, and let $(y,\pi)$ be the output of any run of Algorithm 1 on the reduced one-sided market (the $n+m$ buyers include the virtual buyers $n+j$). Then there is a vector $r\in\mathbb R^M$ with
--   $$
--   r_j-\pi_{n+j}+\rho_j\,y_{n+j}\ \ge\ \rho_j f_j(E_j)\quad (j\in M), \tag{17}
--   $$
--   $$
--   \sum_{j\in M}r_j=\sum_{i\in N}\pi_i . \tag{18}
--   $$
--   After the transformation $r_j\mapsto r_j-\pi_{n+j}$, with $y_{n+j}$ the unsold goods of seller $j$, (17) is (IRs) and (18) is (SBB) for Mechanism 1.
--
--   **Formalization Note** The page writes $p$ for the payments, which are $p:=\pi$ in Mechanism 1. The sum in (18) runs over all $n+m$ buyers. $f_j(E_j)$ is the original stock of seller $j$.
-- source:
--   Hirai & Sato, Polyhedral Clinching Auctions for Two-sided Markets, arXiv:1708.04881v2, p. 11, Lemma 3.4, (17), (18)

import Mathlib
import Definitions.Def_PolyClinch_TwoSided_Clinching

namespace PolyClinch.TwoSided

/-- Lemma 3.4 (Hirai–Sato p. 11). For the output `(y, π)` of Algorithm 1 on the reduced one-sided
market of a valid input, there is a revenue vector `r` with (17)
`r_j − π_{n+j} + ρ_j y_{n+j} ≥ ρ_j f_j(E_j)` for every seller `j`, and (18)
`∑_j r_j = ∑_i π_i` (sum over all `n + m` buyers). -/
theorem lemma_3_4 {n m : ℕ} (E : Finset (Fin n × Fin m)) (ε : ℝ) (hε : 0 < ε)
    (I : PublicInfo E) (hI : Valid E ε I)
    (S₁ : Alg1State (n + m)) (hS₁ : Alg1Outcome (reducedP E I) (extBudget E I) (extBid E I) ε S₁) :
    ∃ r : Fin m → ℝ,
      (∀ j, I.rho j * I.f j (edgesOfSeller E j) ≤
        r j - S₁.pay (Fin.natAdd n j) + I.rho j * S₁.y (Fin.natAdd n j)) ∧
      ∑ j, r j = ∑ i, S₁.pay i := by sorry

end PolyClinch.TwoSided
