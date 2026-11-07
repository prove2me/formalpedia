-- Prove2me | Theorems.Thm_SoftmaxAttnFD_lemma_6_7
-- name    : SoftmaxAttnFD.lemma_6_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:03:25.93277+00:00
-- url     : https://prove2.me/theorems/803bd41c-9298-4930-a98f-2d08517f0d7d
-- title:
--   Lemma 6.7, pp.24–25 — canonical cells
-- statement:
--   Let $d\ge3$ and $k=\lfloor d/2\rfloor$. There is $C_{\rm cell}\ge1$ depending only on $d$ such that for every capped family and all $\emptyset\ne\Sigma'\subseteq\Sigma\subseteq\Sigma_0$:
--
--   1. Every canonical cell $\Delta$ of $P(\Sigma')$ is a closed $(d-1)$-simplex with $d$ rational vertices, and its owner satisfies $\tilde f_{s_\Delta}(u)=E_{\Sigma'}(u)$ on $\Delta$. The union of the cells contains $[-U,U]^{d-1}$.
--   2. $C_\Delta=\bigcup_{\bar v\in\mathrm{vert}(\Delta)}\{s\in\Sigma:\tilde f_s(\bar v)>\tilde f_{s_\Delta}(\bar v)\}$ and $C_\Delta\cap\Sigma'=\emptyset$.
--   3. $P(\Sigma')$ has at most $C_{\rm cell}|\Sigma'|^k$ canonical cells.
--   4. Over all nonempty $\Sigma'\subseteq\Sigma$, at most $(|\Sigma|+d)^{d^2+1}$ distinct owner–cell pairs occur, and for fixed $\Sigma$ each pair has a fixed conflict set, independent of the sample.
--
--   Differences from the source:
--   - generalization: the concrete family of Definition 6.4 → any capped family; reason: the statement uses only the capped-family properties, and Lemma 6.5 shows the concrete family is capped
--   - encoding: closed (d − 1)-dimensional simplex; distinct owner–cell pairs (s_∆, ∆); chains of facets → AffineIndependent vertices with ∆ their convex hull; pairs (owner, vertex tuple), whose count bounds that of pairs (s_∆, ∆); chains by active sets; reason: the hull of finitely many points is closed; ∆ is a function of the tuple; Lemma B.1(b) identifies the two notions of chain
-- source:
--   Huang, Chen, Softmax Attention with Any Temperature in Fixed Dimension, arXiv:2611.06055 (sha256 a60f7609…), Lemma 6.7, pp.24–25; Definitions 6.6, B.7, pp.24, 51

import Definitions.Def_SoftmaxAttnFD_CanonicalCells

namespace SoftmaxAttnFD

/-- **Lemma 6.7** (arXiv:2611.06055, sha256 a60f7609…, pp.24–25), on any capped family.

**Formalization Note** The page states it for the concrete family of Definition 6.4; Lemma 6.5 shows
that family is capped, so this specializes to the page's statement. A cell is the pair (owner, tuple
of `d` projected vertices). The convex hull of `d` affinely independent points is a closed
`(d − 1)`-simplex. Clause (d) counts these tuples, which bounds the printed count of pairs `(s_∆, ∆)`,
since `∆` is a function of the tuple. Its last sentence, on samples `T₁`, `T₂`, holds by the definition
of `conflictSet`, which reads only `S`, the owner and `∆`. `C_cell` depends only on `d`. -/
theorem lemma_6_7 (d : ℕ) (hd : 3 ≤ d) :
    ∃ Ccell : ℕ, 1 ≤ Ccell ∧
      ∀ (F : Family d) (S₀ : Finset ℕ) (U : ℕ), IsCappedFamily F S₀ U →
      ∀ S S' : Finset ℕ, (hS' : S'.Nonempty) → S' ⊆ S → S ⊆ S₀ →
        (∀ (s : ℕ) (vs : Fin d → Fin (d - 1) → ℝ), F.IsCanonicalCell S' s vs →
          AffineIndependent ℝ vs ∧
          (∃ w : Fin d → Fin (d - 1) → ℚ, ∀ i l, vs i l = (w i l : ℝ)) ∧
          (∀ u ∈ cellSet vs, evalSrc (F.src s) u = F.envelope S' hS' u) ∧
          F.conflictSet S s vs =
            (⋃ i : Fin d, {s' | s' ∈ S ∧ evalSrc (F.src s) (vs i) < evalSrc (F.src s') (vs i)}) ∧
          Disjoint (F.conflictSet S s vs) (S' : Set ℕ)) ∧
        (∀ u : Fin (d - 1) → ℝ, InBox U u →
          ∃ (s : ℕ) (vs : Fin d → Fin (d - 1) → ℝ), F.IsCanonicalCell S' s vs ∧ u ∈ cellSet vs) ∧
        Set.encard {c : ℕ × (Fin d → Fin (d - 1) → ℝ) | F.IsCanonicalCell S' c.1 c.2} ≤
          ((Ccell * S'.card ^ (d / 2) : ℕ) : ℕ∞) ∧
        Set.encard {c : ℕ × (Fin d → Fin (d - 1) → ℝ) |
            ∃ T : Finset ℕ, T.Nonempty ∧ T ⊆ S ∧ F.IsCanonicalCell T c.1 c.2} ≤
          (((S.card + d) ^ (d ^ 2 + 1) : ℕ) : ℕ∞) ∧
        (∀ (T₁ T₂ : Finset ℕ) (s : ℕ) (vs₁ vs₂ : Fin d → Fin (d - 1) → ℝ),
          F.IsCanonicalCell T₁ s vs₁ → F.IsCanonicalCell T₂ s vs₂ → cellSet vs₁ = cellSet vs₂ →
          F.conflictSet S s vs₁ = F.conflictSet S s vs₂) := by sorry

end SoftmaxAttnFD
