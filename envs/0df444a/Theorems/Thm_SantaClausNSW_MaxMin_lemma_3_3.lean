-- Prove2me | Theorems.Thm_SantaClausNSW_MaxMin_lemma_3_3
-- name    : SantaClausNSW.MaxMin.lemma_3_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:36:57.660799+00:00
-- url     : https://prove2.me/theorems/8bbc99df-2bca-4e09-b9f9-4e44d6357042
-- title:
--   Lemma 3.3 — conditional on a small configuration S, the rounding fails with probability at most min{1, (32τ/µ)^3}
-- statement:
--   In the setting of §3.1, run the procedure of §3.2: GKPS rounding, then the Shmoys–Tardos assignment. Fix an agent $i$ and a small configuration $S\in S_i$, and write $\Pr_S$ for probability conditional on $S_i=S$. Then
--   $$\Pr_S\big[a^{i,S}(A_i)<\tau\big]\le\Pr_S\big[X_i<2\tau\big]\le\min\Big\{1,\Big(\frac{32\tau}{\mu_{i,S}}\Big)^3\Big\},$$
--   the minimum read as $1$ when $\mu_{i,S}=0$. Summed over small configurations under condition (7), this bounds the failure probability of Lemma 3.1.
--
--   Differences from the source:
--   - reading: the procedure of §3.2 (GKPS rule, sorted order with ties, matching covering the full slots left open) → any valid GKPS rule, and any sorted orders and slot matching chosen as a function of the rounding outcome that satisfy `STValid` on every outcome of positive probability; reason: the paper leaves these choices open, so the lemma is stated for all of them
--   - encoding: Pr_S[·], probability conditional on S_i = S → Pr[· ∧ S_i = S] / Pr[S_i = S]; reason: the definition of conditional probability; Pr[S_i = S] = y_{i,S} > 0
-- source:
--   Chen, Feng, Hu, Li, Zhang, Santa Claus and Weighted Nash Social Welfare with Subadditive Valuations, arXiv:2611.05229 (held version, sha256 98a235d3…), p. 14, Lemma 3.3

import Mathlib
import Definitions.Def_SantaClausNSW_MaxMin_Rounding

namespace SantaClausNSW.MaxMin

/-- **Lemma 3.3** (p. 14). In the setting of §3.1, for the procedure of §3.2 (GKPS rounding with
any valid rule, then the Shmoys–Tardos slot assignment with any valid sorted orders and slot
matching), for every agent `i` and small configuration `S ∈ S_i`, conditional on `S_i = S`:
`Pr_S[a^{i,S}(A_i) < τ] ≤ Pr_S[X_i < 2τ] ≤ min{1, (32τ/µ_{i,S})^3}`. -/
theorem lemma_3_3 {n m : ℕ} (hn : 0 < n) (st : Setting n m) (hst : st.Valid)
    (rule : GKPSRule n m) (hrule : rule.Valid) (ch : STRule n m)
    (hch : ∀ x ∈ (gkpsLaw st rule).support, st.STValid x (ch x).1 (ch x).2)
    (i : Fin n) (S : Finset (Fin m)) (hS : S ∈ st.Sm i) :
    condProbOf (gkpsLaw st rule)
        (fun x => (st.coef i S (stAlloc x (ch x).2 i) : ℝ) < (st.τ : ℝ))
        (fun x => selConfig x i = S) ≤
      condProbOf (gkpsLaw st rule) (fun x => st.Xval x i < 2 * (st.τ : ℝ))
        (fun x => selConfig x i = S) ∧
    condProbOf (gkpsLaw st rule) (fun x => st.Xval x i < 2 * (st.τ : ℝ))
        (fun x => selConfig x i = S) ≤ (st.failTerm i S : ℝ) := by sorry

end SantaClausNSW.MaxMin
