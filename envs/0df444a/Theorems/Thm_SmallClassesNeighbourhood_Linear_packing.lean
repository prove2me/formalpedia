-- Prove2me | Theorems.Thm_SmallClassesNeighbourhood_Linear_packing
-- name    : SmallClassesNeighbourhood.Linear.packing
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T16:35:59.408889+00:00
-- url     : https://prove2.me/theorems/3235d061-26f6-44a7-8bc1-7e2d31cbebc2
-- title:
--   Theorem 9 — packing lemma
-- statement:
--   Let 1≤C≤n be integers, let A have n elements, and let H be a nonempty family of subsets of A with VC dimension d≥1. If R⊆H is C-separated and k=⌈4dn/C⌉≤n, then
--
--   $$|R|\le2\tau_H(k).$$
--
--   Separation is strict distance greater than C, and τ_H is the exact shatter function, not a polynomial envelope. The rounded argument and the factor 2 are retained. This is the set-family packing prerequisite of Corollary 10.
--
--   Differences from the source:
--   - encoding: VC dimension d and k=⌈4dn/C⌉ → Mathlib Finset.vcDim and the natural ceiling of a real quotient; reason: H is nonempty, d≥1 and C≥1, so these agree with the source dimensions and ceiling; k≤n is an explicit hypothesis
-- source:
--   John Sylvester, Viktor Zamaraev, Maksim Zhukovskii, STOC 2027 submission #1126 (October 2026), Theorem 9 (Packing lemma), printed p. 7 (PDF p. 8)

import Definitions.Def_SmallClassesNeighbourhood_Linear_setSystems

namespace SmallClassesNeighbourhood.Linear

theorem packing {V : Type} [Fintype V] [DecidableEq V]
    (A : Finset V) (ℋ ℛ : Finset (Finset V)) (C : ℕ)
    (hC : 1 ≤ C) (hCn : C ≤ A.card) (hH : ℋ.Nonempty)
    (hHA : ∀ X ∈ ℋ, X ⊆ A) (hd : 1 ≤ ℋ.vcDim)
    (hR : ℛ ⊆ ℋ) (hsep : Separated C ℛ)
    (hk : ⌈(4 * (ℋ.vcDim : ℝ) * (A.card : ℝ)) / (C : ℝ)⌉₊ ≤ A.card) :
    ℛ.card ≤ 2 * shatterFunction A ℋ ⌈(4 * (ℋ.vcDim : ℝ) * (A.card : ℝ)) / (C : ℝ)⌉₊ := by sorry

end SmallClassesNeighbourhood.Linear
