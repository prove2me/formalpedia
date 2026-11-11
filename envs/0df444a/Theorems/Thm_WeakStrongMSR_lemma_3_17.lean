-- Prove2me | Theorems.Thm_WeakStrongMSR_lemma_3_17
-- name    : WeakStrongMSR.lemma_3_17
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T08:28:59.98409+00:00
-- url     : https://prove2.me/theorems/44a845c8-315e-41c1-80de-3a01983fe4b6
-- title:
--   Lemma 3.17 — the selected family: $m<102k$ and $\sum_iR_i<51k\lambda$
-- statement:
--   Let $d$ be a metric, $k\ge1$, $\lambda>0$, $S$ a strong set, and $\mathcal C$ a candidate family with nonnegative radii satisfying the following conditions:
--   1. every candidate $(A,s,R)\in\mathcal C$ has a set $E$ with $|E|<h/2$ and $A\setminus E\subseteq B(s,R)$;
--   2. $\mathrm{OPT}_{LP}<17(\mathrm{OPT}+k\lambda)$ for LP (1) on $(S,\mathcal C)$;
--   3. $\lambda\ge\mathrm{OPT}/(2k)$.
--
--   Then the family $Z'=\{(s_i,R_i)\}_{i\le m}$ selected by rounding satisfies
--   $$m<102k\qquad\text{and}\qquad\sum_{i=1}^mR_i<51k\lambda.$$
--   In particular, for $c\ge102$ we have $m\le ck$, so rounding does not abort at its second check.
--
--   Conditions 1 and 2 are the events of Lemmas 3.1 and 3.3, written out as the hypotheses the proof uses.
--
--   Differences from the source:
--   - reading: "on the events of Lemmas 3.1 and 3.3" → explicit hypotheses: each candidate has a set E with |E| < h/2 and A \ E ⊆ B(s, R), and OPT_LP < 17(OPT + kλ); reason: these are exactly the facts of those events that the proof uses
--   - generalization: the strong set and candidate family at the end of sampling → any strong set and any candidate family with nonnegative radii satisfying the hypotheses; reason: covers the sampling outputs, whose radii are estimates md ≥ 0
--   - encoding: the algorithm of §3 described in prose (free choices "any one", "consistently", "a middle value") → the definitions WeakStrongMSR.Sampling/Rounding/Repair/Compress/Test, with ties fixed (insertion order, first conflicting candidate, least-index root, least-index list, ⌊(i+j)/2⌋, u, v = points 0, 1); reason: the paper leaves these choices free; each fixed choice is one admissible run of the paper's algorithm
-- source:
--   Friggstad–Jamshidian–Vakilian, Minimum Sum-of-Radii Clustering with Strong and Weak Oracles (manuscript, STOC 2027 submission, sha256 5f8fbaf3…67e8f92a0), Lemma 3.17, p.17 (PDF 18)

import Mathlib
import Definitions.Def_MinSumClust_IsMetric
import Definitions.Def_MinSumRadiiPTAS_Main_Basic
import Definitions.Def_WeakStrongMSR_Model
import Definitions.Def_WeakStrongMSR_LP
import Definitions.Def_WeakStrongMSR_Rounding

open scoped Classical

set_option autoImplicit false

namespace WeakStrongMSR

/-- **Lemma 3.17** (Friggstad–Jamshidian–Vakilian, *Minimum Sum-of-Radii Clustering with Strong and Weak Oracles*
(manuscript, sha256 5f8fbaf3…67e8f92a0), p.17, PDF p.18).
"On the events of Lemmas 3.1 and 3.3, if λ ≥ OPT/(2k), then the selected family Z′ satisfies
m < 102k and ∑_{i=1}^m R_i < 51kλ. Thus, for c ≥ 102, rounding does not abort at its second
check."

Let `d` be a metric, `k ≥ 1`, `λ > 0`, `S` a strong set and `cands` a candidate family with
nonnegative radii such that (the events of Lemmas 3.1 and 3.3, as used by the proof) every
candidate `(A, s, R)` has a set `E` with `|E| < h/2` and `A ∖ E ⊆ B(s, R)`, and
`OPT_LP < 17(OPT + kλ)`. If `λ ≥ OPT/(2k)`, the selected family `Z′` of rounding has fewer than
`102k` members and total radius below `51kλ`; hence for `c ≥ 102` it has at most `ck` members
(rounding does not abort at its second check).

**Formalization Note.** The probabilistic events are written as the explicit hypotheses the proof
uses; `S` and `cands` are arbitrary (not only sampling outputs). Nonnegative radii hold for every
candidate the algorithm builds (`md ≥ 0`). -/
theorem lemma_3_17 {n : ℕ} (c k h : ℕ) (hk : 1 ≤ k) (lam : ℝ) (hlam : 0 < lam)
    (d : Fin n → Fin n → ℝ) (hd : MinSumClust.IsMetric d) (S : Finset (Fin n))
    (cands : List (Cand n)) (hR : ∀ cd ∈ cands, 0 ≤ cd.R)
    (hE : ∀ cd ∈ cands, ∃ E : Finset (Fin n), (E.card : ℝ) < (h : ℝ) / 2 ∧
      cd.A \ E ⊆ (⟨cd.s, cd.R⟩ : MinSumRadiiPTAS.Main.Ball n).pts d)
    (hLP : lpOpt S cands lam h < 17 * (MinSumRadiiPTAS.Main.msrOpt d k + k * lam))
    (hOPT : MinSumRadiiPTAS.Main.msrOpt d k / (2 * k) ≤ lam) :
    (selectedFamily d S cands lam h).length < 102 * k ∧
      ((selectedFamily d S cands lam h).map Cand.R).sum < 51 * k * lam ∧
      (102 ≤ c → (selectedFamily d S cands lam h).length ≤ c * k) := by sorry

end WeakStrongMSR
