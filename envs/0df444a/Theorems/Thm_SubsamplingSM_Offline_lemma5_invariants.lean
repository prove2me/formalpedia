-- Prove2me | Theorems.Thm_SubsamplingSM_Offline_lemma5_invariants
-- name    : SubsamplingSM.Offline.lemma5_invariants
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T02:57:50.336988+00:00
-- url     : https://prove2.me/theorems/eabc5d30-4bbf-47ff-81d6-7db73afa565a
-- title:
--   Lemma 5 — invariants (P1)–(P3) of Algorithm 2
-- statement:
--   Let $(N,\mathcal I)$ be an independence system, let Algorithm 2 start from a set $O_0\in\mathcal I$, and let $O_u$ be chosen by a minimum-removal rule. For every realization of the coins and after every iteration $t\ge0$ of the while loop:
--   1. **(P1)** $O\in\mathcal I$;
--   2. **(P2)** $S\subseteq O$;
--   3. **(P3)** every element of $O\setminus S$ has not yet been considered, that is, $O\setminus S\subseteq N'$.
--
--   These invariants are used by every later lemma: by (P1) and (P2), $O$ is an extension of $S$, so $p$-extendibility bounds $|O_u|$, and by (P3) the elements of $O\setminus S$ are still candidates.
--
--   Differences from the source:
--   - reading: "throughout Algorithm 2"; "not yet considered" → after every t iterations, for every coin vector; still in N′; reason: paper.md Reading 5
--   - generalization: Algorithm 2 starts from O = OPT, an optimal solution → any starting set O₀ with O₀ ∈ I; reason: paper.md generalization 7: the proof never uses optimality; OPT ∈ I is an instance
--   - generalization: O_u is "the smallest set" of Line 6 (unspecified among ties) → O_u = sel(O, S) for any rule sel with IsMinRemoval I sel; reason: paper.md generalization 8: every choice of smallest set is such a rule
--   - generalization: f non-negative submodular, (N, I) p-extendible (standing assumptions) → no hypothesis on f; I an independence system; reason: the proof uses only the independence-system axioms
-- source:
--   Harshaw, Kazemi, Feldman, Karbasi, The Power of Subsampling in Submodular Maximization, arXiv:2104.02772v1, Lemma 5, p. 11

import Mathlib
import Definitions.Def_SubsamplingSM_Offline_IsIndepSystem
import Definitions.Def_SubsamplingSM_Offline_IsMinRemoval
import Definitions.Def_SubsamplingSM_Offline_alg2Init
import Definitions.Def_SubsamplingSM_Offline_alg2Step

namespace SubsamplingSM.Offline

/-- **Lemma 5 (invariants (P1)–(P3) of Algorithm 2).**
Harshaw, Kazemi, Feldman, Karbasi, *The Power of Subsampling in Submodular Maximization*,
arXiv:2104.02772v1, Lemma 5, p. 11: "The following three properties hold throughout Algorithm 2. (P1) O is an
independent set. (P2) Every element of S is an element of O. (P3) Every element of `O \ S` is an
element not yet considered by Algorithm 2."

Let `I` be an independence system, `O₀ ∈ I` and `sel` a minimum-removal rule. For every coin
vector `b` and every `t`, the state after `t` iterations of Algorithm 2 satisfies
`O ∈ I`, `S ⊆ O` and `O \ S ⊆ N′`.

**Formalization Note.** "Throughout" is "after every iteration, for every coin vector" and "not
yet considered" is "still in `N′`" (paper.md Reading 5). The start is `O₀ ∈ I` instead of OPT
(generalization 7) and `sel` is any minimum-removal rule (generalization 8). Only the
independence-system part of p-extendibility is assumed, and no hypothesis on `f`. -/
theorem lemma5_invariants {α : Type*} [Fintype α] [LinearOrder α]
    (f : Finset α → ℝ) (I : Finset α → Prop) (hI : IsIndepSystem I)
    (sel : Finset α → Finset α → Finset α) (hsel : IsMinRemoval I sel)
    (O₀ : Finset α) (hO₀ : I O₀) :
    ∀ (b : Finset α) (t : ℕ),
      I ((alg2Step f I sel b)^[t] (alg2Init O₀)).O ∧
      ((alg2Step f I sel b)^[t] (alg2Init O₀)).S ⊆ ((alg2Step f I sel b)^[t] (alg2Init O₀)).O ∧
      ((alg2Step f I sel b)^[t] (alg2Init O₀)).O \ ((alg2Step f I sel b)^[t] (alg2Init O₀)).S ⊆
        ((alg2Step f I sel b)^[t] (alg2Init O₀)).N' := by sorry

end SubsamplingSM.Offline
