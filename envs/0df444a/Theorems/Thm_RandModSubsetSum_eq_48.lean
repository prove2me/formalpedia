-- Prove2me | Theorems.Thm_RandModSubsetSum_eq_48
-- name    : RandModSubsetSum.eq_48
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:59:17.862253+00:00
-- url     : https://prove2.me/theorems/a88e187f-d223-41eb-af2b-053960d47c5f
-- title:
--   Equation (48) — residues of uniform coefficients are within $nP_{\rm aux}/Q$ of the auxiliary model
-- statement:
--   Let $a_1,\dots,a_n$ be independent and uniform in $\{0,\dots,Q-1\}$ and let $p_0,\dots,p_7$ be the auxiliary moduli with product $P_{\rm aux}$. The total variation distance between the joint law of the residues $(a_k\bmod p_i)_{i,k}$ and independent uniform residues in $\prod_i\mathbb F_{p_i}^n$ satisfies
--
--   $$\mathrm{TV}\le\frac{nP_{\rm aux}}{Q}.$$
--
--   If moreover $P_{\rm aux}<2^{16}Q\,2^{-10^{-6}n}$ (the prime sizes of ResidueSetup, Appendix C.3), then $\mathrm{TV}\le 2^{16}n\,2^{-10^{-6}n}=n2^{-\eta_{\rm res}n+O(1)}$.
--
--   This transfers the bounds proved in the auxiliary residue model to the integer coefficients of Problem 3.1.
--
--   Differences from the source:
--   - generalization: eight distinct primes p₀, …, p₇ → any pairwise coprime positive moduli; reason: the Chinese remainder theorem needs only coprimality
--   - reading: nP_aux/Q ≤ ε_CRT(n) = n2^{−η_res n+O(1)} → TV ≤ 2^{16} n 2^{−10⁻⁶ n} whenever P_aux < 2^{16} Q 2^{−10⁻⁶ n}; reason: the O(1) is pinned by the prime sizes of Appendix C.3 (P_aux < 2^{16}Q2^{−η_res n}); η_res = 10⁻⁶
-- source:
--   Kim, Kim, Lee, Faster Provable Algorithm For Random Modular Subset Sum, STOC 2027 submission manuscript (sha256 c37a38c7…f89), proof of Theorem 3.2, (48), p. 52; Appendix C.3, p. 68

import Mathlib
import Definitions.Def_RandModSubsetSum_CRT

open scoped BigOperators

namespace RandModSubsetSum

/-- **Equation (48)** (from the auxiliary residue model to integer coefficients). Kim, Kim, Lee, *Faster Provable Algorithm For Random Modular Subset Sum*, STOC 2027 submission
manuscript (sha256 c37a38c7…f89), proof of
Theorem 3.2, (48), p. 52.

For `n` independent uniform coefficients in `{0, …, Q − 1}` and the auxiliary moduli
`p_0, …, p_7` with product `P_aux`, the total variation distance between the joint law of the
residues `(a_k mod p_i)_{i,k}` and independent uniform residues is at most `n P_aux / Q`.

If moreover `P_aux < 2¹⁶ Q 2^{−10⁻⁶ n}` (the prime sizes of ResidueSetup, Appendix C.3, p. 68), the
distance is at most `2¹⁶ n 2^{−10⁻⁶ n} = n 2^{−η_res n + O(1)}` (`η_res = 10⁻⁶`).

**Formalization Note.** The moduli are any pairwise coprime positive integers (the paper's eight
distinct primes are a special case). The `O(1)` of `ε_CRT(n)` is pinned by the prime sizes of
Appendix C.3. -/
theorem eq_48 (n Q : ℕ) (hQ : 1 ≤ Q) (p : Fin 8 → ℕ) (hp : ∀ i, 1 ≤ p i)
    (hcop : Pairwise (fun i j => Nat.Coprime (p i) (p j))) :
    residueTV n Q p ≤ (n : ℝ) * (∏ i, (p i : ℝ)) / (Q : ℝ) ∧
    ((∏ i, (p i : ℝ)) < (2 : ℝ) ^ 16 * Q * (2 : ℝ) ^ (-(1 / 10 ^ 6) * (n : ℝ)) →
      residueTV n Q p ≤ (2 : ℝ) ^ 16 * n * (2 : ℝ) ^ (-(1 / 10 ^ 6) * (n : ℝ))) := by sorry

end RandModSubsetSum
