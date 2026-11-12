-- Prove2me | Theorems.Thm_PoQHierarchy_Main_theorem_6_1
-- name    : PoQHierarchy.Main.theorem_6_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T06:51:36.706316+00:00
-- url     : https://prove2.me/theorems/c6b495d2-1b9e-4f63-ac62-39ce7069f0f7
-- title:
--   Theorem 6.1 — an $n$-player game with $\omega_{ns\text{-}(n-1)}(G)<\omega_q(G)$ [CR17, Thm 8.1]
-- statement:
--   For every $n\ge2$ there exists an $n$-player nonlocal game $G$ (finite question and answer sets, $\mu$ a probability distribution) such that
--   $$\omega_{ns\text{-}(n-1)}(G)<\omega_q(G),$$
--   where $\omega_{ns\text{-}(n-1)}$ is the value of $(n-1)$-local non-signaling strategies (Definition 5.3) and $\omega_q$ the finite-dimensional tensor-product quantum value.
--
--   The paper cites this result from Chao and Reichardt [CR17, Theorem 8.1]. It is the information-theoretic separation that the compiler turns into the separation between $k=n-1$ and $n$ device invocations.
--
--   Differences from the source:
--   - encoding: players [n] and finite question/answer sets I_i, O_i → Fin n, Fin (q i), Fin (o i); reason: every finite set is in bijection with some Fin m; values and correlations are unchanged
--   - encoding: supremum winning probability → sSup in ℝ of the set of winning probabilities; reason: the set is bounded and nonempty whenever every O_i is nonempty; otherwise both sides have no strategy
--   - encoding: shared randomness, arbitrarily many boxes with arbitrary finite alphabets, adaptive local strategies → finite randomness, finitely many boxes with nonempty input alphabets, finite decision trees (first input kept, default input for unasked ports); reason: finite runs use finitely many boxes; values are linear in mixtures; a box with an empty input alphabet can never be queried; by non-signaling unasked ports change no other output
--   - encoding: an n-partite quantum state in a finite-dimensional Hilbert space → a pure state on ℂ^{d_1}⊗⋯⊗ℂ^{d_n} with local POVMs; reason: purification inside a larger finite-dimensional factor changes no correlation
-- source:
--   Kaniuar Bacho, Dominik Leichtle, Atul Singh Arora, Alexandru Cojocaru, STOC 2027 submission #1666 (October 2026), p.42, Theorem 6.1 (citing [CR17, Theorem 8.1]); canonical PDF sha256 3009a0afeb95e5789f4e029db39d01935081f03d75e7fa263cb4b408aed40fb1

import Mathlib
import Definitions.Def_PoQHierarchy_Main_KLocalNS

open QAlgorithms.Complexity
set_option autoImplicit false

namespace PoQHierarchy.Main

/-- Theorem 6.1 ([CR17, Theorem 8.1]), p.42: for all `n ≥ 2` there is an `n`-player nonlocal game
`G` with `ω_{ns-(n-1)}(G) < ω_q(G)`. -/
theorem theorem_6_1 (n : ℕ) (hn : 2 ≤ n) :
    ∃ G : NonlocalGame n, G.IsValid ∧ omegaNS G (n - 1) < omegaQ G := by sorry

end PoQHierarchy.Main
