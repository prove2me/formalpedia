-- Prove2me | Theorems.Thm_PandoraComb_lemma_3_4
-- name    : PandoraComb.lemma_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:09:31.128113+00:00
-- url     : https://prove2.me/theorems/4e3a4a0a-fe89-4cdb-81ae-a270577cf1f6
-- title:
--   Lemma 3.4 (Cancellation Lemma) — $c(h\mid T\cup\{\ell\})-c(\ell\mid T\cup\{h\})=c(h\mid T)-c(\ell\mid T)$
-- statement:
--   Let $c$ be a set function and write $c(x\mid S)=c(S\cup\{x\})-c(S)$ for the marginal cost of $x$ given $S$. For every set $T$ and all elements $h,\ell\notin T$,
--
--   $$c\big(h\mid T\cup\{\ell\}\big)-c\big(\ell\mid T\cup\{h\}\big)=c(h\mid T)-c(\ell\mid T).$$
--
--   The identity is used repeatedly in the induction that proves Lemma 3.3.
--
--   Differences from the source:
--   - generalization: c : 2^[n] → ℝ≥0, T ⊆ [n] → any c : Finset ι → ℝ on the finite subsets of any type ι with decidable equality; reason: the identity is pure algebra and uses no sign of c; the paper's c and [n] are instances
-- source:
--   Berger, Ezra, Feldman & Fusco, Pandora’s Problem with Combinatorial Cost, arXiv:2303.01078v1, Lemma 3.4, p.13

import Definitions.Def_PandoraComb_ClosedForms

namespace PandoraComb

/-- **Lemma 3.4 (Cancellation Lemma)** (arXiv:2303.01078v1, p.13): "For every cost function
c : 2^[n] → ℝ≥0, subset T ⊆ [n] and elements h, ℓ ∈ [n] ∖ T, we have
c(h | T ∪ {ℓ}) − c(ℓ | T ∪ {h}) = c(h | T) − c(ℓ | T)."

**Formalization Note.** `c(x | S) = marginal c x S = c(S ∪ {x}) − c(S)` (p.8); `T ∪ {ℓ}` is
`insert ℓ T`. The cost may take any real values. -/
theorem lemma_3_4 {ι : Type*} [DecidableEq ι] (c : Finset ι → ℝ) (T : Finset ι) (h ℓ : ι)
    (hh : h ∉ T) (hℓ : ℓ ∉ T) :
    marginal c h (insert ℓ T) - marginal c ℓ (insert h T) = marginal c h T - marginal c ℓ T := by sorry

end PandoraComb
