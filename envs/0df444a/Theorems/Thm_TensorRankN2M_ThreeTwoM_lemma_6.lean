-- Prove2me | Theorems.Thm_TensorRankN2M_ThreeTwoM_lemma_6
-- name    : TensorRankN2M.ThreeTwoM.lemma_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T04:16:47.117247+00:00
-- url     : https://prove2.me/theorems/189d4d9d-2d82-436f-8cf7-3ea210b95266
-- title:
--   Lemma 6 (Strong normalization) — a change of basis makes D(e_{0,0}) invertible and {f_i(v)}_i independent for every v ≠ 0
-- statement:
--   Let $\mathbb F$ be an algebraically closed field, $k,l\ge 1$, $m,R\ge 0$, and let $(\alpha_r,\beta_r,C_r)_{0\le r<R}$ be an $R$-rank decomposition of $\langle k,l,m\rangle$ over $\mathbb F$ in which no $\alpha_r$ is identically $0$. Then there are invertible $S\in\mathbb F^{k\times k}$ and $T\in\mathbb F^{l\times l}$ such that the changed decomposition $(\alpha_r(S^{-1}AT),\beta_r(T^{-1}B),SC_r)$ is strongly normalized: writing $D'$, $\mathcal B'$, $f'_i(v)=D'(e_{i,0})\mathcal B'(v)$ for its maps,
--   $$\forall v\in\mathbb F^{l\times m},\ v\ne 0:\ \{f'_i(v):0\le i<k\}\ \text{is linearly independent, and}\ D'(e_{0,0})\ \text{is invertible}.$$
--
--   This is the normalization from which Lemmas 8, 10, 12 and Eq. (1)–(2) start. The two hypotheses on $\mathbb F$ and $\alpha_r$ are the standing assumptions of §2 (p. 2), made without loss of generality before the lemma: passing to the algebraic closure cannot increase rank, and terms with $\alpha_r\equiv 0$ can be removed.
--
--   Differences from the source:
--   - reading: "For a decomposition (W, D, ℬ) of ⟨k,l,m⟩" with no further hypothesis → 𝔽 algebraically closed and no α_r identically 0; reason: these are §2's standing WLOG assumptions (p. 2), in force in §3; without "no α_r ≡ 0" the printed wording is false (a zero term makes D'(e_{0,0}) singular for every change of basis), recorded as finding I1
--   - encoding: "we can change basis such that …" → ∃ S : GL (Fin k) 𝔽, ∃ T : GL (Fin l) 𝔽, (d.changeBasis S T).StronglyNormalized; reason: the change of basis is the one defined on p. 3
--   - encoding: k, l unrestricted → [NeZero k] [NeZero l]; reason: the statement names e_{0,0} and f_0, which exist only for k, l ≥ 1
-- source:
--   Jason Yang, New lower bounds on tensor rank of (n,2,m) matrix multiplication with GPT-6 Astra, STOC 2027 submission (manuscript of October 2026, sha256 6c1df229…), p. 4, Lemma 6 (with the standing assumptions of §2, p. 2)

import Mathlib
import Definitions.Def_TensorRankN2M_ThreeTwoM_Decomposition
import Definitions.Def_TensorRankN2M_ThreeTwoM_Normalization

namespace TensorRankN2M.ThreeTwoM

/-- Lemma 6 (Strong normalization, p. 4), under the standing assumptions of §2 (p. 2): `𝔽` is
algebraically closed and no `α_r` is constant `0`. For a decomposition of ⟨k,l,m⟩ there is a change
of basis `(α_r(S⁻¹AT), β_r(T⁻¹B), S C_r)` after which `{f_i(v) : 0 ≤ i < k}` is linearly
independent for every nonzero `v ∈ 𝔽^{l×m}` and `D(e_{0,0})` is invertible. -/
theorem lemma_6 {𝔽 : Type*} [Field 𝔽] [IsAlgClosed 𝔽] {k l m R : ℕ} [NeZero k] [NeZero l]
    (d : Decomposition 𝔽 k l m R) (hα : ∀ r, d.α r ≠ 0) :
    ∃ (S : GL (Fin k) 𝔽) (T : GL (Fin l) 𝔽), (d.changeBasis S T).StronglyNormalized := by sorry

end TensorRankN2M.ThreeTwoM
