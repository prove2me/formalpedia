-- Prove2me | Theorems.Thm_PrettyGoodShadow_data_processing_Splus
-- name    : PrettyGoodShadow.data_processing_Splus
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:26:47.322206+00:00
-- url     : https://prove2.me/theorems/6bdf0e57-b11c-4b7d-9720-3ab9d24ff4f4
-- title:
--   Proof of Lemma 4.10, display — data processing for $S^+$
-- statement:
--   Let $\mathcal R$ be the channel that takes $s+k$ copies of a state and measures the last $k$ with $\{A,I-A\}$, for $0\preceq A\preceq I$ and $s,k\ge1$. Then, for priors $q,p$,
--
--   $$
--   \mathcal R(S(p,s+k))=S^+(p,s),\qquad \mathcal R(S(q,s+k))=S^+(q,s),
--   $$
--
--   $$
--   D\big(S^+(q,s)\,\big\|\,S^+(p,s)\big)\le D\big(S(q,s+k)\,\big\|\,S(p,s+k)\big).
--   $$
--
--   This is the instance of data processing used to bound the third term in the proof of Lemma 4.10.
--
--   **Formalization Note** The inequality is in the extended reals. The general data-processing inequality is posed elsewhere on the platform and is not stated here.
--
--   Differences from the source:
--   - encoding: D(S⁺(q,s)∥S⁺(p,s)) = D(R(S(q,s+k))∥R(S(p,s+k))) ≤ D(S(q,s+k)∥S(p,s+k)) → two clauses R(S(·,s+k)) = S⁺(·,s), and the inequality between the outer terms; reason: the printed equality follows by rewriting with the two clauses
-- source:
--   Grewal, Pelecanos, Spilecki, Tang, Wright, Pretty good shadow tomography, arXiv:2610.06781 (sha256 bd055b7d…), Proof of Lemma 4.10, p.26

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_PrettyGoodShadow_Delta
import Definitions.Def_PrettyGoodShadow_measureLast

namespace PrettyGoodShadow

open DimFreeShadow (ensembleState)

open QAlgorithms.Papers.Independent.Dependency50.P21 (relativeEntropy)

/-- **Data processing for `S⁺`** (arXiv:2610.06781, sha256 bd055b7d…, display in the proof of Lemma 4.10, p.26). Let
`R` be the channel that takes `s + k` copies of a state and measures the last `k` using `{A, I − A}`. Then
`R(S(p, s + k)) = S⁺(p, s)` for every prior `p`, and `D(S⁺(q, s) ∥ S⁺(p, s)) ≤ D(S(q, s + k) ∥ S(p, s + k))`.

**Formalization Note** `R` is `measureLast`. The inequality is in `EReal`, where `⊤` is the page's `+∞`. It needs no
support hypothesis: if the right side is finite, so is the left. General data processing is posed elsewhere on the
platform and is not stated here; this is the instance the page uses. -/
theorem data_processing_Splus {L d : Type} [Fintype L] [Fintype d] [DecidableEq d]
    (ρ : L → Matrix d d ℂ) (hρ : ∀ x, WildeQIT.IsDensityOperator (ρ x)) (A : Matrix d d ℂ)
    (hA : QAlgorithms.IsEffect A) (q p : L → ℝ) (hq0 : ∀ x, 0 ≤ q x) (hq1 : ∑ x, q x = 1)
    (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1) (s k : ℕ) (hs : 1 ≤ s) (hk : 1 ≤ k) :
    measureLast A s k (ensembleState p ρ (s + k)) = Splus p ρ A s k ∧
    measureLast A s k (ensembleState q ρ (s + k)) = Splus q ρ A s k ∧
    relativeEntropy (Splus q ρ A s k) (Splus p ρ A s k) ≤
      relativeEntropy (ensembleState q ρ (s + k)) (ensembleState p ρ (s + k)) := by sorry

end PrettyGoodShadow
