-- Prove2me | Theorems.Thm_SubmodSparsify_lemma_3_4
-- name    : SubmodSparsify.lemma_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:22:21.741526+00:00
-- url     : https://prove2.me/theorems/31695736-2d5f-4059-abd1-02231da9b7ff
-- title:
--   Lemma 3.4 — residual bounds for $\Delta(S,U) = f(S) - f^{\to}(S\setminus U, \bar S \setminus U)$
-- statement:
--   Let $V$ be a finite ground set and $f : 2^V \to \mathbb R_{\ge 0}$ submodular with $f(\emptyset) = f(V) = 0$; write $\bar S = V \setminus S$. Then for all $S, T \subseteq V$,
--   $$f(S) - f(T) \le f^{\to}(S \setminus T, \bar S) + f^{\to}(S \cap T, T \setminus S),$$
--   and for all $S, U \subseteq V$ the residual $\Delta(S, U) := f(S) - f^{\to}(S \setminus U, \bar S \setminus U)$ satisfies
--
--   1. $0 \le \Delta(S, U) \le f^{\to}(S \cap U, \bar S) + f^{\to}(S, U \setminus S)$;
--   2. $\Delta(S, U)$ is monotone non-decreasing in $U$;
--   3. $\Delta(S, \emptyset) = 0$ and $\Delta(S, V) = f(S)$.
--
--   The residual measures how much is lost when $f(S)$ is approximated by a block min-cut that fixes only the coordinates outside the free set $U$; the bound in item 1 reduces it to two monotone submodular block min-cuts.
--
--   Differences from the source:
--   - encoding: finite ground set V, subsets of V, S̄ → finite type α, Finset α, Sᶜ; reason: Lean representation; same instances
--   - encoding: Δ(S, U) as a named quantity; "monotone with respect to U" → Δ written out as f S − blockMinCut f (S \ U) (Sᶜ \ U); monotone as U ⊆ U′ → Δ(S, U) ≤ Δ(S, U′); reason: the paper's definition inline; monotone means non-decreasing (Appendix C, p.60)
-- source:
--   Bao, Cai, Chen, He, Zhang, Nearly Optimal Submodular Sparsification, with and without Cardinality Constraints, arXiv:2606.20777 (version held, sha256 358242d6…), Lemma 3.4, p.17 (PDF p.19)

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_SubmodSparsify_blockMinCut

namespace SubmodSparsify

/-- **Lemma 3.4** (p.17): the residual bounds.

Bao, Cai, Chen, He, Zhang, *Nearly Optimal Submodular Sparsification, with and without
Cardinality Constraints*, arXiv:2606.20777 (version held), Lemma 3.4, p.17.

For a nonnegative submodular `f` on a finite ground set `V` with `f(∅) = f(V) = 0`: for all
`S, T`, `f(S) − f(T) ≤ f→(S \ T, S̄) + f→(S ∩ T, T \ S)`; and the residual
`Δ(S, U) := f(S) − f→(S \ U, S̄ \ U)` satisfies (1) `0 ≤ Δ(S, U) ≤ f→(S ∩ U, S̄) + f→(S, U \ S)`,
(2) `Δ(S, U)` is monotone non-decreasing in `U`, (3) `Δ(S, ∅) = 0` and `Δ(S, V) = f(S)`.

**Formalization Note.** `V` is a finite type `α`, `S̄ = Sᶜ`; all block min-cuts here have
disjoint arguments. "Monotone" is non-decreasing (Appendix C, p.60). -/
theorem lemma_3_4 {α : Type} [Fintype α] [DecidableEq α] (f : Finset α → ℝ)
    (hf0 : ∀ S, 0 ≤ f S) (hf : NonmonotoneSubmod.Shared.Submodular f)
    (hempty : f ∅ = 0) (huniv : f Finset.univ = 0) :
    (∀ S T : Finset α,
      f S - f T ≤ blockMinCut f (S \ T) Sᶜ + blockMinCut f (S ∩ T) (T \ S)) ∧
    (∀ S U : Finset α, 0 ≤ f S - blockMinCut f (S \ U) (Sᶜ \ U) ∧
      f S - blockMinCut f (S \ U) (Sᶜ \ U) ≤
        blockMinCut f (S ∩ U) Sᶜ + blockMinCut f S (U \ S)) ∧
    (∀ S U U' : Finset α, U ⊆ U' →
      f S - blockMinCut f (S \ U) (Sᶜ \ U) ≤ f S - blockMinCut f (S \ U') (Sᶜ \ U')) ∧
    (∀ S : Finset α, f S - blockMinCut f (S \ ∅) (Sᶜ \ ∅) = 0 ∧
      f S - blockMinCut f (S \ Finset.univ) (Sᶜ \ Finset.univ) = f S) := by sorry

end SubmodSparsify
