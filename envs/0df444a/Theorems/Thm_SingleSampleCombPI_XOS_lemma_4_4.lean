-- Prove2me | Theorems.Thm_SingleSampleCombPI_XOS_lemma_4_4
-- name    : SingleSampleCombPI.XOS.lemma_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T09:11:01.858613+00:00
-- url     : https://prove2.me/theorems/7e8c3126-8612-431e-8cb0-8b25a6651a01
-- title:
--   Lemma 4.4 — the configuration objective is normalized, nonnegative, monotone and submodular
-- statement:
--   Let $b_1,\dots,b_n$ be indivisible-item buyer types with supporting prices. On the ground set $N=\{e_{i,S}: i\in[n], S\subseteq[m]\}$ define
--   $$f(I)=\sum_{j=1}^m\ \max_{e_{i,S}\in I,\ S\ni j}q_{i,j}(S)\qquad(I\subseteq N),$$
--   with empty maxima $0$. Then $f(\emptyset)=0$, $f\ge0$, $f$ is monotone, and $f$ is submodular (diminishing returns) on all subsets of $N$, not only on encodings of partial allocations.
--
--   It makes Algorithm 4 an instance of online submodular maximization over the partition matroid with parts $P_i=\{e_{i,S}\}$.
--
--   Differences from the source:
--   - encoding: a valuation v with its supporting-price map q_v (and, for computation, oracle access) → a record Buyer m with fields v, q (supporting-price oracle) and d (demand oracle) on vectors in ℝ^m, bundles as indicator vectors; reason: values off A^m are never used; the paper's per-valuation map q_v is the record's q
--   - encoding: q_{i,j}(S) for a bundle S → the supporting-price oracle at the indicator vector 1_S; reason: bundles are indicator vectors; same values
-- source:
--   Shuchi Chawla, Trung Dang, STOC 2027 submission #30 (October 2026), SHA-256 d6ed330221fdb64a0d8f70c7d0abbd3346ee1cb8f9e101a745f7e1e57d35230e, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/30.pdf, printed p. 19 / PDF p. 21, Lemma 4.4

import Mathlib
import Definitions.Def_SingleSampleCombPI_XOS_Algorithms
import Definitions.Def_SubsamplingSM_Offline_IsSubmodular

namespace SingleSampleCombPI.XOS

/-- **Lemma 4.4** (Chawla–Dang, STOC 2027 submission #30, printed p. 19 / PDF p. 21).  For
indivisible-item buyers with supporting prices, the configuration objective
`f(I) = ∑_j max_{e_{i,S} ∈ I, S ∋ j} q_{i,j}(S)` on all subsets `I` of the configuration ground
set is normalized, nonnegative, monotone and submodular. -/
theorem lemma_4_4 {n m : ℕ} (b : Fin n → Buyer m) (hb : ∀ i, (b i).Valid .indivisible) :
    configObj b ∅ = 0 ∧ (∀ I, 0 ≤ configObj b I) ∧
    (∀ I J : Finset (Config n m), I ⊆ J → configObj b I ≤ configObj b J) ∧
    SubsamplingSM.Offline.IsSubmodular (configObj b) := by sorry

end SingleSampleCombPI.XOS
