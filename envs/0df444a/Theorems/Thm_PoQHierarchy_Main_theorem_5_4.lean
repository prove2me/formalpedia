-- Prove2me | Theorems.Thm_PoQHierarchy_Main_theorem_5_4
-- name    : PoQHierarchy.Main.theorem_5_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T06:51:58.990141+00:00
-- url     : https://prove2.me/theorems/1a08771f-70cb-491f-a214-05db37ecc1ff
-- title:
--   Theorem 5.4 — $\omega_{qc\text{-}I}(G)\le\omega_{ns\text{-}|I|}(G)$
-- statement:
--   Let $G$ be an $n$-player nonlocal game and $I\subseteq[n]$ any subset, with $k=|I|$. Then
--   $$\omega_{qc\text{-}I}(G)\le\omega_{ns\text{-}k}(G).$$
--
--   Every correlation of an $I$-quantum commuting operator strategy (Definition 5.1, possibly infinite-dimensional) is realised by a $k$-local non-signaling strategy (Definition 5.3). This links the quantum resource that the soundness theorems produce to a model in which separating games are known.
--
--   Differences from the source:
--   - encoding: players [n] and finite question/answer sets I_i, O_i → Fin n, Fin (q i), Fin (o i); reason: every finite set is in bijection with some Fin m; values and correlations are unchanged
--   - encoding: supremum winning probability → sSup in ℝ of the set of winning probabilities; reason: the set is bounded and nonempty whenever every O_i is nonempty; otherwise both sides have no strategy
--   - encoding: possibly infinite-dimensional Hilbert space H → any complex Hilbert space in Lean's lowest universe, with bounded operators; reason: the finitely many operators of a strategy generate a separable cyclic subspace, so no correlation is lost
--   - encoding: shared randomness, arbitrarily many boxes with arbitrary finite alphabets, adaptive local strategies → finite randomness, finitely many boxes with nonempty input alphabets, finite decision trees (first input kept, default input for unasked ports); reason: finite runs use finitely many boxes; values are linear in mixtures; a box with an empty input alphabet can never be queried; by non-signaling unasked ports change no other output
--   - encoding: Pr[a|x] = ⟨Ω|∏P|Ω⟩ (a real number) → the real part of the complex inner product in the winning probability; reason: the correlation is real, so the real part equals it
--   - generalization: an n-player nonlocal game, n ≥ 2 players (§3.2, p.19) → any number n of players (no hypothesis 2 ≤ n); reason: the Lean statement covers more games; restricted to n ≥ 2 it is exactly the source's statement
-- source:
--   Kaniuar Bacho, Dominik Leichtle, Atul Singh Arora, Alexandru Cojocaru, STOC 2027 submission #1666 (October 2026), p.30, Theorem 5.4; canonical PDF sha256 3009a0afeb95e5789f4e029db39d01935081f03d75e7fa263cb4b408aed40fb1

import Mathlib
import Definitions.Def_PoQHierarchy_Main_ICO
import Definitions.Def_PoQHierarchy_Main_KLocalNS

open QAlgorithms.Complexity
set_option autoImplicit false

namespace PoQHierarchy.Main

/-- Theorem 5.4, p.30: for every `I ⊆ [n]` with `k = |I|`, `ω_{qc-I}(G) ≤ ω_{ns-k}(G)`. -/
theorem theorem_5_4 {n : ℕ} (G : NonlocalGame n) (hG : G.IsValid) (I : Finset (Fin n)) :
    omegaQC G I ≤ omegaNS G I.card := by sorry

end PoQHierarchy.Main
