-- Prove2me | Theorems.Thm_SubsamplingSM_Offline_lemma9_linear_bound
-- name    : SubsamplingSM.Offline.lemma9_linear_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T03:01:12.892373+00:00
-- url     : https://prove2.me/theorems/0f103704-dbbd-44b6-bf02-b6aca035f3d8
-- title:
--   Lemma 9 — deterministic bound for linear objectives (corrected: $f(u)$ read as $f(u\mid\emptyset)$)
-- statement:
--   Let $f$ be linear, $(N,\mathcal I)$ an independence system, $O_0\in\mathcal I$ the starting set of Algorithm 2 and $O_u$ chosen by a minimum-removal rule. For every realization of the coins, the final values of Algorithm 2 satisfy
--   $$f(S)\ \ge\ f(O_0)-\sum_{u\in N}\big(|O_u|-Y_u\big)\,f(u\mid\emptyset),\qquad f(u\mid\emptyset)=f(\{u\})-f(\emptyset).$$
--
--   With $O_0=\mathrm{OPT}$ this is Lemma 9, the linear analogue of Lemma 6; with Lemmas 10 and 8 it gives the ratio $p$.
--
--   **Formalization Note** The paper writes $f(u)$; read as $f(\{u\})$ the lemma is false when $f(\emptyset)>0$, which linearity allows. The coefficient $|O_u|-Y_u$ is a real number and can equal $-1$.
--
--   Differences from the source:
--   - correction: f(u) in Σ_u [|O_u| − Y_u] f(u) → f(u | ∅) = f({u}) − f(∅); reason: false as printed: N = {x, y, z}, x < y < z, I = subsets of {x} and of {y, z} (2-extendible), f(S) = 1 + w(S) with w = (3, 1, 1) (non-negative, linear), OPT = {x}, coins b = {y, z}: Algorithm 2 rejects x (O_x = {x}) and accepts y, z (Y_y = Y_z = 1), so f(S) = 3 < 4 = f(OPT) − Σ[|O_u| − Y_u] f({u}); the proof's own step 'since f is linear, f(v) ≤ f(u)' (p. 16) is about marginals, and both readings agree when f(∅) = 0
--   - reading: S, O_u, S_u, X_u (Y_u): the final values of Algorithm 2 (p. 12) → fields of alg2Run after n iterations; X_u = considered, Y_u = yIndicator; reason: paper.md Reading 6: the loop stops within n iterations and later iterations are the identity
--   - generalization: Algorithm 2 starts from O = OPT, an optimal solution → any starting set O₀ with O₀ ∈ I; reason: paper.md generalization 7: the proof never uses optimality; OPT ∈ I is an instance
--   - generalization: O_u is "the smallest set" of Line 6 (unspecified among ties) → O_u = sel(O, S) for any rule sel with IsMinRemoval I sel; reason: paper.md generalization 8: every choice of smallest set is such a rule
--   - generalization: f non-negative linear, (N, I) p-extendible (standing assumptions) → f linear; I an independence system; reason: the proof uses neither non-negativity nor p-extendibility
-- source:
--   Harshaw, Kazemi, Feldman, Karbasi, The Power of Subsampling in Submodular Maximization, arXiv:2104.02772v1, Lemma 9, p. 15

import Mathlib
import Definitions.Def_SubsamplingSM_Offline_IsLinearSetFn
import Definitions.Def_SubsamplingSM_Offline_IsIndepSystem
import Definitions.Def_SubsamplingSM_Offline_IsMinRemoval
import Definitions.Def_SubsamplingSM_Offline_yIndicator

namespace SubsamplingSM.Offline

/-- **Lemma 9 (deterministic bound for linear objectives), corrected: `f(u)` read as
`f(u | ∅)`.**
Harshaw, Kazemi, Feldman, Karbasi, *The Power of Subsampling in Submodular Maximization*,
arXiv:2104.02772v1, Lemma 9, p. 15: "`f(S) ≥ f(OPT) − Σ_{u∈N} [|Ou| − Yu]f(u)`."

Let `f` be linear, `I` an independence system, `O₀ ∈ I` and `sel` a minimum-removal rule.
For every coin vector `b`, the final values of Algorithm 2 satisfy
`f(S) ≥ f(O₀) − Σ_u (|O_u| − Y_u) · (f({u}) − f(∅))`.

**Formalization Note.** Correction (paper.md Correction 1): the page's `f(u)` is the marginal
`f(u | ∅) = f({u}) − f(∅)`. Read as `f({u})`, the lemma is false when `f(∅) > 0`, which
linearity allows: on `N = {x, y, z}` (`x < y < z`), `I` the subsets of `{x}` and of
`{y, z}`, `f(S) = 1 + w(S)` with `w = (3, 1, 1)`, `OPT = {x}` and `b = {y, z}`, Algorithm 2
gives `f(S) = 3 < 4 = f(OPT) − Σ_u [|O_u| − Y_u] f({u})`. The proof's own steps use the
marginal ("since f is linear, `f(v) ≤ f(u)`", p. 16). The coefficient `|O_u| − Y_u` is real and
may be `−1`. `O₀ ∈ I` replaces OPT (generalization 7) and `sel` is any minimum-removal rule
(generalization 8); non-negativity of `f` and p-extendibility of `I` are not assumed. -/
theorem lemma9_linear_bound {α : Type*} [Fintype α] [LinearOrder α]
    (f : Finset α → ℝ) (hf : IsLinearSetFn f) (I : Finset α → Prop) (hI : IsIndepSystem I)
    (sel : Finset α → Finset α → Finset α) (hsel : IsMinRemoval I sel)
    (O₀ : Finset α) (hO₀ : I O₀) :
    ∀ b : Finset α,
      f O₀ - ∑ u : α, ((((alg2Run f I sel O₀ b).Ou u).card : ℝ) - yIndicator f I sel O₀ b u) *
          (f {u} - f ∅)
        ≤ f (alg2Run f I sel O₀ b).S := by sorry

end SubsamplingSM.Offline
