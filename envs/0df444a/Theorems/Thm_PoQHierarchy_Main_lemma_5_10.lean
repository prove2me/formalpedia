-- Prove2me | Theorems.Thm_PoQHierarchy_Main_lemma_5_10
-- name    : PoQHierarchy.Main.lemma_5_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T06:51:59.408333+00:00
-- url     : https://prove2.me/theorems/5277686d-a3de-477a-a1f7-4ffb48b248f6
-- title:
--   Lemma 5.10 — an $I'$-strategy for $G^L$ collapses to an $I$-strategy for $G$ with the same value
-- statement:
--   Let $G$ be an $n$-player nonlocal game, $L\ge1$, and $G^L$ the $(nL+1)$-player game of p.36: $L$ independent copies of $G$ and a last player who receives the fixed question $\perp$ and selects the copy $j\in[L]$ to be checked. For $I\subseteq[n]$ let
--   $$I'=\bigcup_{l=1}^L\bigl((l-1)n+I\bigr)\subseteq[nL+1].$$
--   Then for every $I'$-quantum commuting operator strategy $S^L$ for $G^L$ there is an $I$-quantum commuting operator strategy $S$ for $G$ with
--   $$\Pr[S^L\text{ wins }G^L]=\Pr[S\text{ wins }G].$$
--
--   In the proof of Theorem 5.11 this lemma transfers the soundness bound for the repeated compiled game back to $G$.
--
--   Differences from the source:
--   - encoding: players [n] and finite question/answer sets I_i, O_i → Fin n, Fin (q i), Fin (o i); reason: every finite set is in bijection with some Fin m; values and correlations are unchanged
--   - encoding: possibly infinite-dimensional Hilbert space H → any complex Hilbert space in Lean's lowest universe, with bounded operators; reason: the finitely many operators of a strategy generate a separable cyclic subspace, so no correlation is lost
--   - encoding: Pr[a|x] = ⟨Ω|∏P|Ω⟩ (a real number) → the real part of the complex inner product in the winning probability; reason: the correlation is real, so the real part equals it
--   - encoding: player (l−1)n+i of G^L, question ⊥, answer j ∈ [L] → player l·n+i (0-based), Fin 1, Fin L; reason: a relabelling of the players and of the last player's sets
--   - generalization: an n-player nonlocal game, n ≥ 2 players (§3.2, p.19) → any number n of players (no hypothesis 2 ≤ n); reason: the Lean statement covers more games; restricted to n ≥ 2 it is exactly the source's statement
-- source:
--   Kaniuar Bacho, Dominik Leichtle, Atul Singh Arora, Alexandru Cojocaru, STOC 2027 submission #1666 (October 2026), p.36, Lemma 5.10; canonical PDF sha256 3009a0afeb95e5789f4e029db39d01935081f03d75e7fa263cb4b408aed40fb1

import Mathlib
import Definitions.Def_PoQHierarchy_Main_RepGame
import Definitions.Def_PoQHierarchy_Main_ICO

open QAlgorithms.Complexity
set_option autoImplicit false

namespace PoQHierarchy.Main

/-- Lemma 5.10, p.36: for `L ≥ 1`, `I ⊆ [n]` and `I' = ⋃_l ((l-1)n + I)`, every `I'`-quantum
commuting operator strategy `S^L` for `G^L` has an `I`-quantum commuting operator strategy `S` for
`G` with `Pr[S^L wins G^L] = Pr[S wins G]`. -/
theorem lemma_5_10 {n : ℕ} (G : NonlocalGame n) (hG : G.IsValid) (L : ℕ) (hL : 1 ≤ L)
    (I : Finset (Fin n)) (SL : ICOStrategy (n * L + 1) (G.rep L).q (G.rep L).o (NonlocalGame.repSet L I)) :
    ∃ S : ICOStrategy n G.q G.o I, SL.win (G.rep L) = S.win G := by sorry

end PoQHierarchy.Main
