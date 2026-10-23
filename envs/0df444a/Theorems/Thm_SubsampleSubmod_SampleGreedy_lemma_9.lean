-- Prove2me | Theorems.Thm_SubsampleSubmod_SampleGreedy_lemma_9
-- name    : SubsampleSubmod.SampleGreedy.lemma_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:08:58.494338+00:00
-- url     : https://prove2.me/theorems/a1aafbbd-7c6d-4213-ac45-92965f092779
-- title:
--   Lemma 9, p. 15 — for linear f with f(∅) = 0, f(S) ≥ f(OPT) − Σ_{u∈𝒩} [|O_u| − Y_u] f(u)
-- statement:
--   Let $f$ be linear with $f(\emptyset) = 0$, $(\mathcal N, \mathcal I)$ an independence system, $T \in \mathcal I$ (playing the role of OPT) and $B$ any outcome of the coins. For the final sets of Algorithm 2 run from $O = T$, let $Y_u = 1$ if $u$ was added to $S$ and $u \notin O$ at the beginning of the iteration in which $u$ was considered, and $Y_u = 0$ otherwise. Then
--   $$f(S) \;\ge\; f(T) \;-\; \sum_{u \in \mathcal N} \big[\,|O_u| - Y_u\,\big]\, f(\{u\}).$$
--
--   This is the sharper analogue of Lemma 6 for linear objectives, used in the proof of the $p$-approximation.
--
--   **Formalization Note** The hypothesis $f(\emptyset) = 0$ is added. As printed, without it, the inequality is false for linear functions with $f(\emptyset) > 0$: when an element $v$ leaves $O$ the value drops by $f(\{v\}) - f(\emptyset)$, not by $f(\{v\})$, and $|O_u| - Y_u = -1$ is possible. A five-element instance with $f(\emptyset) = 5$ gives $f(S) = 10 < 15$. Theorem 1's linear clause does not carry this hypothesis. $|O_u| - Y_u$ is computed in $\mathbb R$.
-- source:
--   Harshaw et al., arXiv:2104.02772v1, p. 15, Lemma 9 (definition of Y_u, p. 15; proof pp. 15–16)

import Mathlib
import Definitions.Def_SubsampleSubmod_SampleGreedy_Analysis

namespace SubsampleSubmod.SampleGreedy

/-- Lemma 9 (p. 15), with `f(∅) = 0` added. For linear `f` with `f(∅) = 0` and the final sets of
Algorithm 2 run from an independent `T` (OPT) with coin flips `B`:
`f(S) ≥ f(T) − ∑_{u ∈ 𝒩} (|O_u| − Y_u) f({u})`, where `Y_u = 1` iff `u` is added to `S` and `u ∉ O`
at the beginning of the iteration in which `u` is considered. As printed (without `f(∅) = 0`) the
inequality can fail. -/
theorem lemma_9 {α : Type} [Fintype α] [LinearOrder α] (f : Finset α → ℝ)
    (I : Finset α → Prop) (hlin : IsLinear f) (hf_empty : f ∅ = 0) (hI : IsIndepSystem I)
    (T : Finset α) (hT : I T) (B : Finset α) :
    f T - ∑ u : α, ((((alg2 f I T B).Ou u).card : ℝ) - (if u ∈ (alg2 f I T B).Y then (1 : ℝ) else 0)) *
        f {u} ≤
      f (alg2 f I T B).S := by sorry

end SubsampleSubmod.SampleGreedy
