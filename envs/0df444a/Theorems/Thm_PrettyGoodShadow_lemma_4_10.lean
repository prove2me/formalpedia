-- Prove2me | Theorems.Thm_PrettyGoodShadow_lemma_4_10
-- name    : PrettyGoodShadow.lemma_4_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:27:12.599206+00:00
-- url     : https://prove2.me/theorems/71fe2c5e-c84e-4622-97aa-cf79b6f493e6
-- title:
--   Lemma 4.10 — one-step bound on $\sum_x q_x\Delta_x(p,s)$
-- statement:
--   Let $p$ and $q$ be priors with $\operatorname{supp}(q)\subseteq\operatorname{supp}(p)$ and let $0\preceq A\preceq I$. For all $s,k\ge1$,
--
--   $$
--   \sum_x q_x\Delta_x(p,s)\le D\big(S(q,s+k)\,\big\|\,S(p,s+k)\big)-D\big(S(q,s)\,\big\|\,S(p,s)\big)+\log\frac{s+k+1}{s+1}.
--   $$
--
--   Summing over the copy numbers telescopes this bound into Lemma 4.9.
--
--   **Formalization Note** Under the support hypothesis both relative entropies on the right are finite, so they enter through their real values and the subtraction is in $\mathbb R$.
--
--   Differences from the source:
--   - encoding: real-valued D on supports → D.toReal for the two values on the right; reason: the support hypothesis makes both values finite, so the real value is the true one
-- source:
--   Grewal, Pelecanos, Spilecki, Tang, Wright, Pretty good shadow tomography, arXiv:2610.06781 (sha256 bd055b7d…), Lemma 4.10, p.24

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_PrettyGoodShadow_Delta

namespace PrettyGoodShadow

open DimFreeShadow (ensembleState)

open QAlgorithms.Papers.Independent.Dependency50.P21 (relativeEntropy)

/-- **Lemma 4.10** (arXiv:2610.06781, sha256 bd055b7d…, p.24). Let `p` and `q` be priors with `supp(q) ⊆ supp(p)`.
Then, for every `s, k ≥ 1`,
`Σ_x q_x Δ_x(p, s) ≤ D(S(q, s + k) ∥ S(p, s + k)) − D(S(q, s) ∥ S(p, s)) + log((s + k + 1)/(s + 1))`.

**Formalization Note** The relative entropies on the right are finite under `supp(q) ⊆ supp(p)`, since
`S(q, n) ⪯ c S(p, n)` with `c = max_{p_x > 0} q_x / p_x`; the `.toReal` therefore reads their true values and the
subtraction is in `ℝ`. A label with `q_x = 0` carries weight `0`, and a label with `q_x > 0` has `p_x > 0`, so
`Delta` is finite wherever it counts. `0 ⪯ A ⪯ I` is the standing assumption of §4.1, p.19. -/
theorem lemma_4_10 {L d : Type} [Fintype L] [Fintype d] [DecidableEq d] (ρ : L → Matrix d d ℂ)
    (hρ : ∀ x, WildeQIT.IsDensityOperator (ρ x)) (A : Matrix d d ℂ) (hA : QAlgorithms.IsEffect A)
    (q p : L → ℝ) (hq0 : ∀ x, 0 ≤ q x) (hq1 : ∑ x, q x = 1) (hp0 : ∀ x, 0 ≤ p x)
    (hp1 : ∑ x, p x = 1) (hsupp : ∀ x, p x = 0 → q x = 0) (s k : ℕ) (hs : 1 ≤ s) (hk : 1 ≤ k) :
    ∑ x, q x * Delta p ρ A s k x ≤
      (relativeEntropy (ensembleState q ρ (s + k)) (ensembleState p ρ (s + k))).toReal -
        (relativeEntropy (ensembleState q ρ s) (ensembleState p ρ s)).toReal +
        Real.log (((s : ℝ) + k + 1) / ((s : ℝ) + 1)) := by sorry

end PrettyGoodShadow
