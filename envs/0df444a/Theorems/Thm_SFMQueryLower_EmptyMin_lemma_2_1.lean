-- Prove2me | Theorems.Thm_SFMQueryLower_EmptyMin_lemma_2_1
-- name    : SFMQueryLower.EmptyMin.lemma_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:21:57.829196+00:00
-- url     : https://prove2.me/theorems/3fbb0897-00c0-4095-87d7-78fde3af78fb
-- title:
--   Lemma 2.1 — nesting preserves submodularity and the full range
-- statement:
--   Let $V$ be a finite set and let $P,R\subseteq V$ be disjoint and nonempty. Let $w$ be a positive integer. Suppose $g:2^{V\setminus(P\cup R)}\to\mathbb R$ is submodular and $-1\le g(T)\le w-1$ on every inner subset. For the nesting operation $h$ defined above,
--   $$h\text{ is submodular},\qquad -1\le h(S)\le w|V|(|V|-1)\quad(S\subseteq V).$$
--   This is the range-preserving nesting result used to construct the layered hard family. The inner function is constrained only on its own ground set.
--
--   **Formalization Note** Positive integer weights use positive natural numbers; the upper endpoint uses real subtraction, not truncated natural subtraction. No equal-block-size hypothesis is present.
--
--   Differences from the source:
--   - encoding: finite labeled ground sets and their subsets → Fin n and Finset (Fin n); reason: bijections relabel every finite source instance
--   - encoding: g takes values in [-1,w-1] and w is a positive integer → a real-valued g on the actual inner subtype with pointwise interval bounds and a positive natural w; reason: the same inner functions and positive integer weights are represented
-- source:
--   James Fox, Randomized Query Lower Bounds for Submodular Function Minimization, STOC 2027 submission #292 (October 2026), Lemma 2.1, printed p. 7 / PDF p. 8; proof Appendix A.1, printed pp. 13–14 / PDF pp. 14–15

import Definitions.Def_SFMQueryLower_EmptyMin_Nesting

set_option autoImplicit false
open scoped ENNReal

namespace SFMQueryLower.EmptyMin

/-- Fox, Lemma 2.1, printed p.7 / PDF p.8; proof Appendix A.1, pp.13–14.
`Fin n` relabels the finite set `V`; the inner function lives only on `V \ (P ∪ R)`.
The integer weight is represented by a positive natural number. -/
theorem lemma_2_1 (n : ℕ) (P R : Finset (Fin n))
    (hP : P.Nonempty) (hR : R.Nonempty) (hPR : Disjoint P R)
    (w : ℕ) (hw : 0 < w) (g : Finset (InnerGround P R) → ℝ)
    (hg : NonmonotoneSubmod.Shared.Submodular g)
    (hgrange : ∀ S, -1 ≤ g S ∧ g S ≤ (w : ℝ) - 1) :
    NonmonotoneSubmod.Shared.Submodular (nest P R w g) ∧
      ∀ S : Finset (Fin n), -1 ≤ nest P R w g S ∧
        nest P R w g S ≤ (w : ℝ) * n * ((n : ℝ) - 1) := by sorry

end SFMQueryLower.EmptyMin
