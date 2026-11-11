-- Prove2me | Theorems.Thm_RandomColorMix269_Mixing_lemma_5_6
-- name    : RandomColorMix269.Mixing.lemma_5_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:03:42.557926+00:00
-- url     : https://prove2.me/theorems/ea4517db-3783-4c73-8890-ba6d0f6c468f
-- title:
--   Lemma 5.6 — $\mathrm{Ent}_\mu f\le4b^{-(3k+1)}\sum_v\mathrm{Ent}^v_\mu f$ on $k$ coordinates
-- statement:
--   Let $\mu$ be a probability distribution on $k\ge1$ coordinates with connected conditional supports that is $b$-marginally bounded for some $b\in(0,1/2]$. Then for every non-negative function $f$
--   $$
--   \mathrm{Ent}_\mu[f]\le4b^{-(3k+1)}\sum_v\mathrm{Ent}^v_\mu(f).
--   $$
--   This is the local step of Proposition 5.15, applied to components of size $O(\ln n)$.
--
--   Differences from the source:
--   - encoding: distribution on k ≥ 1 coordinates → mass function on Fin q^V with |V| = k ≥ 1; reason: finite coordinate alphabets relabel into Fin q
-- source:
--   Zhidan Li, Kuan Yang, STOC 2027 submission #269 (October 2026), PDF sha256 467638f1abc0f57df1bc0dcd9abfd308eb90ddbaf4947dac3eefa5f293ac6f05, p.29, Lemma 5.6

import Definitions.Def_RandomColorMix269_Mixing_Entropy

open scoped Classical BigOperators
set_option autoImplicit false

namespace RandomColorMix269.Mixing

/-- Lemma 5.6, p.29, including k=1 and the zero test function. -/
theorem lemma_5_6 {V : Type*} [Fintype V] [DecidableEq V] {q : ℕ}
    (hk : 1 ≤ Fintype.card V) (μ : (V → Fin q) → ℝ) (hμ : MarkovMixing.IsDist μ)
    (b : ℝ) (hb : 0 < b) (hbhalf : b ≤ 1 / 2)
    (hCS : ConnectedConditionalSupports μ) (hMB : MarginalBounded μ b) :
    SingleFactorization μ (4 * ((b ^ (3 * Fintype.card V + 1))⁻¹)) := by sorry

end RandomColorMix269.Mixing
