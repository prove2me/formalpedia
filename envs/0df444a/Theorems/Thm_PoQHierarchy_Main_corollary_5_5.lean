-- Prove2me | Theorems.Thm_PoQHierarchy_Main_corollary_5_5
-- name    : PoQHierarchy.Main.corollary_5_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T06:52:02.557097+00:00
-- url     : https://prove2.me/theorems/51dfd6c3-0912-4bc3-b980-f63af04c6872
-- title:
--   Corollary 5.5 — $\max_{|I|=k}\omega_{qc\text{-}I}(G)\le\omega_{ns\text{-}k}(G)$
-- statement:
--   Let $G$ be an $n$-player nonlocal game and $0\le k\le n$. Then
--   $$\max_{I\subseteq[n],\ |I|=k}\omega_{qc\text{-}I}(G)\le\omega_{ns\text{-}k}(G).$$
--
--   Together with the main soundness bound (Corollary 5.13), this bounds what a prover with $k$ device invocations can achieve in a compiled game by the $k$-local non-signaling value.
--
--   Differences from the source:
--   - encoding: players [n] and finite question/answer sets I_i, O_i → Fin n, Fin (q i), Fin (o i); reason: every finite set is in bijection with some Fin m; values and correlations are unchanged
--   - encoding: supremum winning probability → sSup in ℝ of the set of winning probabilities; reason: the set is bounded and nonempty whenever every O_i is nonempty; otherwise both sides have no strategy
--   - encoding: possibly infinite-dimensional Hilbert space H → any complex Hilbert space in Lean's lowest universe, with bounded operators; reason: the finitely many operators of a strategy generate a separable cyclic subspace, so no correlation is lost
--   - encoding: shared randomness, arbitrarily many boxes with arbitrary finite alphabets, adaptive local strategies → finite randomness, finitely many boxes with nonempty input alphabets, finite decision trees (first input kept, default input for unasked ports); reason: finite runs use finitely many boxes; values are linear in mixtures; a box with an empty input alphabet can never be queried; by non-signaling unasked ports change no other output
--   - encoding: Pr[a|x] = ⟨Ω|∏P|Ω⟩ (a real number) → the real part of the complex inner product in the winning probability; reason: the correlation is real, so the real part equals it
--   - encoding: max over I ⊆ [n] with |I| = k → indexed supremum ⨆ over the subtype {I : Finset (Fin n) // I.card = k}; reason: for k ≤ n the index set is finite and nonempty, so the supremum is the maximum
--   - generalization: an n-player nonlocal game, n ≥ 2 players (§3.2, p.19) → any number n of players (no hypothesis 2 ≤ n); reason: the Lean statement covers more games; restricted to n ≥ 2 it is exactly the source's statement
-- source:
--   Kaniuar Bacho, Dominik Leichtle, Atul Singh Arora, Alexandru Cojocaru, STOC 2027 submission #1666 (October 2026), p.30, Corollary 5.5; canonical PDF sha256 3009a0afeb95e5789f4e029db39d01935081f03d75e7fa263cb4b408aed40fb1

import Mathlib
import Definitions.Def_PoQHierarchy_Main_ICO
import Definitions.Def_PoQHierarchy_Main_KLocalNS

open QAlgorithms.Complexity
set_option autoImplicit false

namespace PoQHierarchy.Main

/-- Corollary 5.5, p.30: for `0 ≤ k ≤ n`, `max_{I ⊆ [n], |I| = k} ω_{qc-I}(G) ≤ ω_{ns-k}(G)`. The
maximum over the finite nonempty family `{I : |I| = k}` is written as an indexed supremum. -/
theorem corollary_5_5 {n : ℕ} (G : NonlocalGame n) (hG : G.IsValid) (k : ℕ) (hk : k ≤ n) :
    (⨆ I : {I : Finset (Fin n) // I.card = k}, omegaQC G I.1) ≤ omegaNS G k := by sorry

end PoQHierarchy.Main
