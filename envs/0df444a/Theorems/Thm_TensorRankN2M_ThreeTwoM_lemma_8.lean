-- Prove2me | Theorems.Thm_TensorRankN2M_ThreeTwoM_lemma_8
-- name    : TensorRankN2M.ThreeTwoM.lemma_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T04:17:09.78619+00:00
-- url     : https://prove2.me/theorems/7ae4286a-5d42-4667-90df-bf2b1e5f8f47
-- title:
--   Lemma 8 — dim(f_0(S) + ⋯ + f_{k−1}(S)) ≥ dim(S) + (k − 1) for every nonzero subspace S
-- statement:
--   Let $\mathbb F$ be algebraically closed, $k,l\ge 1$, and let $(\alpha_r,\beta_r,C_r)_{0\le r<R}$ be a strongly normalized $R$-rank decomposition of $\langle k,l,m\rangle$ over $\mathbb F$, with $f_i(x)=D(e_{i,0})\mathcal B(x)$. Then for every nonzero subspace $S\subseteq\mathbb F^{l\times m}$,
--   $$\dim\big(f_0(S)+\dots+f_{k-1}(S)\big)\ \ge\ \dim(S)+(k-1).$$
--
--   In §4.1 it is applied to the subspace $S$ of Lemma 12 (with $k=3$) to show $\Delta\ge 2$ when that subspace is nonzero.
--
--   Differences from the source:
--   - reading: the lemma's sentence carries no hypotheses on the decomposition → 𝔽 algebraically closed, the decomposition strongly normalized; reason: §2's standing assumptions (p. 2) and the strong normalization of Lemma 6 (§3, p. 4), after which the lemma is stated, are in force; §2's other assumption, no α_r identically 0, is not a separate hypothesis because strong normalization implies it (D(e_{0,0}) invertible)
--   - encoding: f_0(S) + ⋯ + f_{k−1}(S) → ⨆ i : Fin k, S.map (d.f i); dimensions → Module.finrank in ℕ, k − 1 with k ≥ 1; reason: Lean convention, same subspace and numbers
--   - encoding: k, l unrestricted → [NeZero k] [NeZero l]; reason: the statement names f_0, which exists only for k, l ≥ 1
-- source:
--   Jason Yang, New lower bounds on tensor rank of (n,2,m) matrix multiplication with GPT-6 Astra, STOC 2027 submission (manuscript of October 2026, sha256 6c1df229…), p. 4, Lemma 8

import Mathlib
import Definitions.Def_TensorRankN2M_ThreeTwoM_Decomposition
import Definitions.Def_TensorRankN2M_ThreeTwoM_Normalization

namespace TensorRankN2M.ThreeTwoM

/-- Lemma 8 (p. 4): for a strongly normalized decomposition of ⟨k,l,m⟩ (under the standing
assumption of §2 that `𝔽` is algebraically closed; §2's other assumption, no `α_r` constant `0`,
is implied by strong normalization), every nonzero subspace
`S ⊆ 𝔽^{l×m}` satisfies `dim(f_0(S) + ⋯ + f_{k−1}(S)) ≥ dim(S) + (k − 1)`. -/
theorem lemma_8 {𝔽 : Type*} [Field 𝔽] [IsAlgClosed 𝔽] {k l m R : ℕ} [NeZero k] [NeZero l]
    (d : Decomposition 𝔽 k l m R) (hd : d.StronglyNormalized)
    (S : Submodule 𝔽 (Matrix (Fin l) (Fin m) 𝔽)) (hS : S ≠ ⊥) :
    Module.finrank 𝔽 S + (k - 1) ≤ Module.finrank 𝔽 ↥(⨆ i : Fin k, S.map (d.f i)) := by sorry

end TensorRankN2M.ThreeTwoM
