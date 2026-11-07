-- Prove2me | Theorems.Thm_SoftmaxAttnFD_lemma_7_2
-- name    : SoftmaxAttnFD.lemma_7_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:04:12.248718+00:00
-- url     : https://prove2.me/theorems/528208aa-cbf0-4aa4-ab80-645cc3e74c4b
-- title:
--   Lemma 7.2, p.27 — hits
-- statement:
--   Let $d\ge3$, let the perturbed family be capped over $\Sigma_0$ and $U$, and let $|\tilde f_s(u)-f_s(u)|\le1/8$ for $s\in\Sigma_0$ on the box. A source $s$ is a **hit** for a target $(u,b)$, $\|u\|_\infty\le U$, if $b+\tilde f_s(u)\ge-L$. Then:
--
--   1. A hit has original score $b+f_s(u)\ge-L-1/8$.
--   2. A source in $\Sigma_0$ that is not a hit has original score below $-L+1/8$.
--   3. Let $\emptyset\ne\Sigma'\subseteq\Sigma\subseteq\Sigma_0$, and let $\Delta$ be a canonical cell of $P(\Sigma')$ containing $u$. If no source in $\Sigma'$ hits, every hit in $\Sigma$ belongs to $C_\Delta$.
--
--   Differences from the source:
--   - generalization: the concrete family of Definition 6.4 with Lemma 6.5(a); rational targets → any capped family with the bound 1/8 as a hypothesis; real targets and real L; reason: the statement uses only those properties, and Lemma 6.5 gives both for the concrete family
-- source:
--   Huang, Chen, Softmax Attention with Any Temperature in Fixed Dimension, arXiv:2611.06055 (sha256 a60f7609…), Lemma 7.2, p.27

import Definitions.Def_SoftmaxAttnFD_CanonicalCells

namespace SoftmaxAttnFD

/-- **Lemma 7.2** (arXiv:2611.06055, sha256 a60f7609…, p.27), on any capped family with
Lemma 6.5(a) as a hypothesis. A source `s` is a hit for the target `(u, b)` if `b + f̃_s(u) ≥ −L`.

**Formalization Note** `y` is the original family and `F` the perturbed one. The target lies in the box
(§7.1, p.26: "The instance bounds satisfy that definition for both sources and target positions").
Lemma 6.5 gives the concrete perturbed family both hypotheses, so this specializes to the page's
statement. -/
theorem lemma_7_2 (d : ℕ) (hd : 3 ≤ d) (F : Family d) (y : ℕ → Src d) (S₀ : Finset ℕ) (U : ℕ)
    (hF : IsCappedFamily F S₀ U)
    (hpert : ∀ s ∈ S₀, ∀ u : Fin (d - 1) → ℝ, InBox U u →
      |evalSrc (F.src s) u - evalSrc (y s) u| ≤ 1 / 8)
    (u : Fin (d - 1) → ℝ) (hu : InBox U u) (b L : ℝ) :
    (∀ s ∈ S₀, -L ≤ b + evalSrc (F.src s) u → -L - 1 / 8 ≤ b + evalSrc (y s) u) ∧
    (∀ s ∈ S₀, ¬ -L ≤ b + evalSrc (F.src s) u → b + evalSrc (y s) u < -L + 1 / 8) ∧
    (∀ (S S' : Finset ℕ) (o : ℕ) (vs : Fin d → Fin (d - 1) → ℝ), S'.Nonempty → S' ⊆ S → S ⊆ S₀ →
      F.IsCanonicalCell S' o vs → u ∈ cellSet vs →
      (∀ s ∈ S', ¬ -L ≤ b + evalSrc (F.src s) u) →
      ∀ s ∈ S, -L ≤ b + evalSrc (F.src s) u → s ∈ F.conflictSet S o vs) := by sorry

end SoftmaxAttnFD
