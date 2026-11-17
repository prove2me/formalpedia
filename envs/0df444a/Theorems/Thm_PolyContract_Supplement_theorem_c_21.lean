-- Prove2me | Theorems.Thm_PolyContract_Supplement_theorem_c_21
-- name    : PolyContract.Supplement.theorem_c_21
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:06:55.094984+00:00
-- url     : https://prove2.me/theorems/16b26841-3339-4e01-9adf-84df1cab7758
-- title:
--   Theorem C.21 — the parameter rule satisfies (W1)–(W6) and (T1)–(T3) at every step $k\ge1$
-- statement:
--   Let $k\ge1$ and let $\mu^{\mathrm{in}}\in\mathcal F$ have length at least $k+2$; build the levels of the comb gadget by the parameter rule. If the hypotheses (W1)–(W6) of Lemma C.15 hold at the steps $0\to1,\dots,k-1\to k$, then at the step $k\to k+1$:
--
--   1. the hypotheses (W1)–(W6) of Lemma C.15 hold, and
--   2. the hypotheses (T1)–(T3) of Theorem C.18 hold with $(e_t,e_l)=(b_k,\tau_{2,k})$.
--
--   With the base case (Proposition C.22) this shows by induction that one explicit rule works at every step.
--
--   Differences from the source:
--   - encoding: the levels and the hypotheses of Lemma C.15 and Theorem C.18 → one ambient element type; marginals at a chosen full-plane best response; reason: the full-plane best response exists and is unique (published milestone)
-- source:
--   Klimm, Lippke, Warode, The Complexity of Continuous Contract Design over Polymatroids, arXiv:2611.04934 (version of November 3, 2026, sha256 18cfc0a5…), Theorem C.21, App. C.7, p.67 (PDF p.68)

import Mathlib
import Definitions.Def_PolyContract_IsComb
import Definitions.Def_PolyContract_Supplement_HypC15

set_option autoImplicit false

namespace PolyContract.Supplement

/-- **Theorem C.21** (Klimm, Lippke, Warode, arXiv:2611.04934, version of November 3, 2026, sha256
18cfc0a5…, App. C.7, p.67): let `k ≥ 1`, and let `µ^in ∈ F` have length at least `k + 2`. Assume
that the hypotheses of Lemma C.15 hold at the steps `0 → 1, …, k − 1 → k`. Then at the step
`k → k + 1`, the hypotheses of Lemma C.15 and those of Theorem C.18 with `(e_t, e_l) = (b_k, τ_{2,k})`
hold.

**Formalization Note** The levels are those of Definition C.11 built by the parameter rule of
Definition C.12; "the hypotheses of Lemma C.15 at the step `i → i + 1`" is `HypC15 µ^in i`, and
those of Theorem C.18 are (T1)–(T3) at the step `k → k + 1`. -/
theorem theorem_c_21 (μin : List ℕ) (hμ : PerturbedPow8 μin) (k : ℕ) (hk : 1 ≤ k)
    (hlen : k + 2 ≤ μin.length) (hW : ∀ i < k, HypC15 μin i) :
    HypC15 μin k ∧ HypT1 μin k (bnew k) (tau2 k) ∧ HypT2 μin k (tau2 k) ∧ HypT3 μin k (tau2 k) := by sorry

end PolyContract.Supplement
