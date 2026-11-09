-- Prove2me | Theorems.Thm_SwitchingRegret_Dyadic_lemma_4_3
-- name    : SwitchingRegret.Dyadic.lemma_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:27:34.239547+00:00
-- url     : https://prove2.me/theorems/20a82671-46d1-4296-aa6c-ebfd38ab881e
-- title:
--   Lemma 4.3 — maximal dyadic cover
-- statement:
--   Let $T>K\ge2$, let $\ell\in[0,1]^{T\times K}$ be deterministic before any seed is drawn, and let $u$ be a deterministic arm sequence with at most $S<T$ switches. For every $1\le\tau\le n\le T$, let $D(\tau,n)$ contain all canonical dyadic intervals in $[\tau,n]$ on which $u$ is constant and that are maximal under inclusion. Then this family partitions $[\tau,n]$, the comparator is constant on every member, and
--   $$|D(\tau,n)|\le(S+1)L.$$
--   The partition clause asserts that every round in the prefix belongs to exactly one member and no round outside it belongs to a member. This is the combinatorial cover used in the continuation bounds.
--
--   Differences from the source:
--   - encoding: arms in [K] and finite round sequences → arms in Fin K and natural-indexed functions restricted to rounds 1 through T; reason: relabeling is bijective and values outside the horizon are ignored; NeZero K follows from K ≥ 2
--   - generalization: a reached epoch start tau_j → every deterministic prefix start tau with 1 ≤ tau ≤ n ≤ T; reason: every reached epoch prefix is one such integer interval
-- source:
--   Mengxiao Zhang, Toward Optimal Switching Regret for Multi-Armed Bandits with Oblivious Adversary, 2026 preprint, STOC 2027 submission #99, SHA-256 70dc03d632eeb5878823d984fc755157b34301d8189bbd7a6087570a8f8a7fee, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/99.pdf, Lemma 4.3, PDF p. 12 (printed p. 11).

import Definitions.Def_SwitchingRegret_Dyadic_Continuation

open MeasureTheory

namespace SwitchingRegret.Dyadic

theorem lemma_4_3 {K T : ℕ} (hK : 2 ≤ K) (hT : K < T)
    (S : ℕ) (hS : S < T) (u : ℕ → Fin K) (hu : switches T u ≤ S)
    (tau n : ℕ) (htau : 1 ≤ tau) (hn : tau ≤ n) (hnT : n ≤ T) :
    (∀ t : ℕ, (∃! J : Dyad T, J ∈ cover T tau n u ∧ t ∈ rounds J) ↔ t ∈ Finset.Icc tau n) ∧
      (∀ J ∈ cover T tau n u, constantOn u J) ∧
      (cover T tau n u).card ≤ (S + 1) * L T := by sorry

end SwitchingRegret.Dyadic
