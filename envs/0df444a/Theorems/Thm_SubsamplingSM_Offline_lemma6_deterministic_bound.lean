-- Prove2me | Theorems.Thm_SubsamplingSM_Offline_lemma6_deterministic_bound
-- name    : SubsamplingSM.Offline.lemma6_deterministic_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T02:58:29.469198+00:00
-- url     : https://prove2.me/theorems/22058b4f-81be-4c3b-915b-8ec0f17db687
-- title:
--   Lemma 6 — deterministic lower bound on $f(S)$
-- statement:
--   Let $f$ be submodular, $(N,\mathcal I)$ an independence system, $O_0\in\mathcal I$ the starting set of Algorithm 2 and $O_u$ chosen by a minimum-removal rule. For every realization of the coins, the final values of Algorithm 2 satisfy
--   $$f(S)\ \ge\ f(S\cup O_0)-\sum_{u\in N}|O_u\setminus S|\cdot f(u\mid S_u).$$
--
--   With $O_0=\mathrm{OPT}$ this is Lemma 6; together with Lemmas 7 and 8 it gives the ratio for submodular objectives.
--
--   Differences from the source:
--   - reading: S, O_u, S_u, X_u (Y_u): the final values of Algorithm 2 (p. 12) → fields of alg2Run after n iterations; X_u = considered, Y_u = yIndicator; reason: paper.md Reading 6: the loop stops within n iterations and later iterations are the identity
--   - generalization: Algorithm 2 starts from O = OPT, an optimal solution → any starting set O₀ with O₀ ∈ I; reason: paper.md generalization 7: the proof never uses optimality; OPT ∈ I is an instance
--   - generalization: O_u is "the smallest set" of Line 6 (unspecified among ties) → O_u = sel(O, S) for any rule sel with IsMinRemoval I sel; reason: paper.md generalization 8: every choice of smallest set is such a rule
--   - generalization: f non-negative submodular, (N, I) p-extendible (standing assumptions) → f submodular; I an independence system; reason: the proof uses only (1) and the independence-system axioms, not non-negativity or p-extendibility
-- source:
--   Harshaw, Kazemi, Feldman, Karbasi, The Power of Subsampling in Submodular Maximization, arXiv:2104.02772v1, Lemma 6, p. 12

import Mathlib
import Definitions.Def_SubsamplingSM_Offline_IsSubmodular
import Definitions.Def_SubsamplingSM_Offline_IsIndepSystem
import Definitions.Def_SubsamplingSM_Offline_IsMinRemoval
import Definitions.Def_SubsamplingSM_Offline_alg2Run

namespace SubsamplingSM.Offline

/-- **Lemma 6 (deterministic lower bound on `f(S)`).**
Harshaw, Kazemi, Feldman, Karbasi, *The Power of Subsampling in Submodular Maximization*,
arXiv:2104.02772v1, Lemma 6, p. 12: "`f(S) ≥ f(S ∪ OPT) − Σ_{u∈N} |Ou \ S| · f(u | Su)`."

Let `f` be submodular, `I` an independence system, `O₀ ∈ I` and `sel` a minimum-removal
rule. For every coin vector `b`, the final values `S`, `O_u`, `S_u` of Algorithm 2 satisfy
`f(S) ≥ f(S ∪ O₀) − Σ_u |O_u \ S| · f(u | S_u)`.

**Formalization Note.** `S`, `O_u`, `S_u` are the fields of the final state `alg2Run`
(paper.md Reading 6); `O₀ ∈ I` replaces OPT (generalization 7) and `sel` is any
minimum-removal rule (generalization 8). Non-negativity of `f` and p-extendibility of `I` are
not assumed. -/
theorem lemma6_deterministic_bound {α : Type*} [Fintype α] [LinearOrder α]
    (f : Finset α → ℝ) (hf : IsSubmodular f) (I : Finset α → Prop) (hI : IsIndepSystem I)
    (sel : Finset α → Finset α → Finset α) (hsel : IsMinRemoval I sel)
    (O₀ : Finset α) (hO₀ : I O₀) :
    ∀ b : Finset α,
      f ((alg2Run f I sel O₀ b).S ∪ O₀) -
          ∑ u : α, (((alg2Run f I sel O₀ b).Ou u \ (alg2Run f I sel O₀ b).S).card : ℝ) *
            marg f ((alg2Run f I sel O₀ b).Su u) u
        ≤ f (alg2Run f I sel O₀ b).S := by sorry

end SubsamplingSM.Offline
