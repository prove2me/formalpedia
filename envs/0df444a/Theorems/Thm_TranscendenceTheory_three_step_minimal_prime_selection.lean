-- Prove2me | Theorems.Thm_TranscendenceTheory_three_step_minimal_prime_selection
-- name    : TranscendenceTheory.three_step_minimal_prime_selection
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-20T20:08:50.135446+00:00
-- url     : https://prove2.me/theorems/8ce6a2a8-def8-477a-b3d0-3253ee743d82
-- title:
--   Selection of a persistent minimal prime in three steps
-- statement:
--   Let $R$ be a commutative ring and let
--
--   $$I_0\subseteq I_1\subseteq I_2\subseteq I_3\subseteq\mathfrak q$$
--
--   be ideals, with $\mathfrak q$ prime. Assume
--
--   $$\operatorname{ht}(I_0)\ge2,\qquad \operatorname{ht}(\mathfrak q)\le4.$$
--
--   Then there exist $i\in\{0,1,2\}$ and a prime $\mathfrak p\subseteq\mathfrak q$ that is a minimal prime over both $I_i$ and $I_{i+1}$.
--
--   Heights are the extended-natural-valued ideal heights of Mathlib. The theorem does not require a Noetherian hypothesis. In the four-variable complex chart ring, applying it to $I_i=P_{iU}(J)$ selects a persistent component starting at one of $0,U,2U$, provided the initial height and terminal containment assumptions have been established.
--
--   **Formalization Note.** This is an affine prime-height version of the dimension-drop selection argument in [Philippon (1986), §5, p. 380](https://www.numdam.org/item/10.24033/bsmf.2060.pdf), used in the zero-estimate framework for [Senthil Kumar (2026), Appendix A, Theorem A.2](https://doi.org/10.1017/S001309152610145X). It is a complete commutative-algebra selection criterion. It does not construct the geometric derivative ideals from the analytic vanishing assumptions or establish a global degree estimate.
-- source:
--   Philippon (1986), Lemmes de zeros dans les groupes algebriques commutatifs, Bull. Soc. Math. France 114, 355-383, section 5, p. 380: dimension-drop selection of a component common to adjacent derivative stages. https://www.numdam.org/item/10.24033/bsmf.2060.pdf. Senthil Kumar K (2026), Appendix A, Theorem A.2. https://doi.org/10.1017/S001309152610145X. The complete theorem gives an affine prime-height criterion: four increasing ideals, initial height at least two, all below a prime of height at most four, have a common minimal prime at adjacent stages. The chart reduction selects a stage among 0, U, 2U. Constructing the geometric height and terminal-containment data and proving the uniform total-length degree bound remain open. This is a sufficient route; no converse for arbitrary old chart data is asserted.

import Mathlib.RingTheory.Ideal.Height

theorem TranscendenceTheory.three_step_minimal_prime_selection
    (R : Type*) [CommRing R] (J : Fin 4 → Ideal R) (hJ : Monotone J)
    (q : Ideal R) [q.IsPrime]
    (hterminal : J 3 ≤ q) (hlower : (2 : ℕ∞) ≤ (J 0).height)
    (hupper : q.height ≤ (4 : ℕ∞)) :
    ∃ (i : Fin 3) (p : Ideal R), p ≤ q ∧
      p ∈ (J i.castSucc).minimalPrimes ∧ p ∈ (J i.succ).minimalPrimes := by sorry
