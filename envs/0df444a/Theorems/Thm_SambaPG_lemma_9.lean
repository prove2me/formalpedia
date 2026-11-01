-- Prove2me | Theorems.Thm_SambaPG_lemma_9
-- name    : SambaPG.lemma_9
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T11:37:06.026786+00:00
-- url     : https://prove2.me/theorems/de41cf7a-0382-4c20-b9af-295baae640a3
-- title:
--   Lemma 9 — $\sum_{s<T}A/(B+Cs)\le(A/C)\log T$ (corrected: $T\ge3$)
-- statement:
--   Let $A,B,C>0$ with $B>2C$. For every integer $T\ge3$,
--
--   $$
--   \sum_{s=0}^{T-1}\frac{A}{B+Cs}\le\frac{A}{C}\log T .
--   $$
--
--   With $A=N$, $B=2N$, $C=\alpha\Delta$ it turns the bound (13) into the $\frac{N}{\alpha\Delta}\log T$ term of Theorem 1.
--
--   Differences from the source:
--
--   - correction: T ∈ ℕ → T ≥ 3; reason: false for T = 1 (left side A/B > 0 = log 1) and for T = 2 with A = C = 1, B = 2.1 (1/2.1 + 1/3.1 ≈ 0.799 > log 2 ≈ 0.693); the proof integrates to T − 1 instead of T. For T ≥ 3 the bound holds
-- source:
--   Denisov & Walton, Regret Analysis of a Markov Policy Gradient Algorithm for Multi-arm Bandits, arXiv:2007.10229v3, Lemma 9, p.26 (proof §A.6, p.26)

import Mathlib

namespace SambaPG

/-- **Lemma 9 (a harmonic-type sum is at most `(A/C) log T`; corrected: `T ≥ 3`).**
Denisov & Walton, arXiv:2007.10229v3, Lemma 9, p.26 (proof §A.6, p.26).

For positive constants `A, B, C` with `B > 2C` and every integer `T ≥ 3`,
`Σ_{s=0}^{T−1} A/(B + Cs) ≤ (A/C) log T`.

**Formalization Note.** As printed the lemma is stated for all `T ∈ ℕ`; it is false for `T = 1`
(left side `A/B > 0 = log 1`) and for `T = 2` with `A = C = 1`, `B = 2.1`
(`1/2.1 + 1/3.1 ≈ 0.799 > log 2 ≈ 0.693`). The proof's integral bound should run to `T`, not
`T − 1`; with that, the bound holds for `T ≥ 3`. -/
theorem lemma_9 {A B C : ℝ} (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hBC : 2 * C < B)
    {T : ℕ} (hT : 3 ≤ T) :
    ∑ s ∈ Finset.range T, A / (B + C * s) ≤ A / C * Real.log T := by sorry

end SambaPG
