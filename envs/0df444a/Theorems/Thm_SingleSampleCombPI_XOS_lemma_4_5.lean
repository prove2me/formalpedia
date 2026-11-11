-- Prove2me | Theorems.Thm_SingleSampleCombPI_XOS_lemma_4_5
-- name    : SingleSampleCombPI.XOS.lemma_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T09:10:42.736226+00:00
-- url     : https://prove2.me/theorems/4d720809-4861-4a45-b6df-c8b9e6ac3e84
-- title:
--   Lemma 4.5 — demand maximizers maximize the marginal contribution
-- statement:
--   Let $b_1,\dots,b_n$ be indivisible-item buyer types with supporting prices, let $I$ be a set of configurations and $p_j=\max_{e_{i',S}\in I,\,S\ni j}q_{i',j}(S)$ (empty maximum $0$). For buyer $i$ put $U_i(S)=v_i(S)-p(S)$ and $\Delta_i(S)=f(I\cup\{e_{i,S}\})-f(I)$. Then
--   $$\max_{S\subseteq[m]}U_i(S)=\max_{S\subseteq[m]}\Delta_i(S),$$
--   and every maximizer of $U_i$ is also a maximizer of $\Delta_i$.
--
--   With $I$ the encoded allocation of the earlier buyers this says that Algorithm 4 is exactly greedy on the configuration objective.
--
--   Differences from the source:
--   - generalization: I = I_{i−1}, the encoded partial allocation of the buyers processed before i → an arbitrary finite set I of configurations; reason: the identity holds for every configuration set; I = I_{i−1} is the source's case
--   - encoding: a valuation v with its supporting-price map q_v (and, for computation, oracle access) → a record Buyer m with fields v, q (supporting-price oracle) and d (demand oracle) on vectors in ℝ^m, bundles as indicator vectors; reason: values off A^m are never used; the paper's per-valuation map q_v is the record's q
-- source:
--   Shuchi Chawla, Trung Dang, STOC 2027 submission #30 (October 2026), SHA-256 d6ed330221fdb64a0d8f70c7d0abbd3346ee1cb8f9e101a745f7e1e57d35230e, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/30.pdf, printed p. 20 / PDF p. 22, Lemma 4.5

import Mathlib
import Definitions.Def_SingleSampleCombPI_XOS_Algorithms

namespace SingleSampleCombPI.XOS

/-- **Lemma 4.5** (Chawla–Dang, STOC 2027 submission #30, printed p. 20 / PDF p. 22).  At the
prices `p_j = p_j(I)` of a configuration set `I`, the maximum buyer-wise utility
`U_i(S) = v_i(S) - p(S)` equals the maximum marginal contribution
`Δ_i(S) = f(I ∪ {e_{i,S}}) - f(I)`, and every maximizer of `U_i` maximizes `Δ_i`. -/
theorem lemma_4_5 {n m : ℕ} (b : Fin n → Buyer m) (hb : ∀ i, (b i).Valid .indivisible)
    (I : Finset (Config n m)) (i : Fin n) :
    Finset.univ.sup' Finset.univ_nonempty (utilU b I i) =
        Finset.univ.sup' Finset.univ_nonempty (margΔ b I i) ∧
    ∀ S, (∀ T, utilU b I i T ≤ utilU b I i S) → ∀ T, margΔ b I i T ≤ margΔ b I i S := by sorry

end SingleSampleCombPI.XOS
