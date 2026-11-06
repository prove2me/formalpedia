-- Prove2me | Theorems.Thm_TIESched_lemma_5_12
-- name    : TIESched.lemma_5_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:47:40.09259+00:00
-- url     : https://prove2.me/theorems/3960de0e-6ba3-4ae1-91a4-6d6e58badb9a
-- title:
--   Lemma 5.12 — the left-smoothed utility interactions vanish for $|J|\ge m$
-- statement:
--   Let $(x,u)$ be a feasible, truthful, padding-invariant fractional mechanism family and $I$ a compatible positive integration. Fix $|J|\ge m$, $D=m|J|$, and let $\kappa:\mathbb R^D\to\mathbb R$ be nonnegative and smooth, with integral one and compact support contained in $(0,\infty)^D$. The left convolutions $V^J_i*_L\kappa$ of the zero-extended utility interactions satisfy all the hypotheses of Lemma 5.8. Consequently
--   $$(V^J_i*_L\kappa)(p)=0\qquad\text{for all }i\in[m]\text{ and all }p\in\mathbb R^D.$$
--
--   Differences from the source:
--   - reading: the left convolution ∗_L as a Lebesgue integral (p.29) → (10): (f ∗_L κ)(p) = I_D(s ↦ f(s)κ(p − s)); reason: App. A.2 (p.41) states that the proof of Lemma 5.12 applies with (10), and the interactions need not be measurable (footnote 2, Remark 5.15)
--   - generalization: the functionals I_D of Lemma A.1 → any family I satisfying properties (1)–(5) of Lemma A.1; reason: the argument (pp.40–41) uses only these properties; it specializes to the functionals of Lemma A.1
--   - reading: padding-invariant (T_v defined with one chosen fresh label per job set) → invariance for every fresh label k ∉ S; reason: the proof of Lemma 5.7 (p.25) views a job k ∈ J as the padding job of S∖{k}, which needs invariance for that label; the family of Lemma 5.6 is relabeling-equivariant, so the choice is immaterial (p.24)
--   - encoding: rules x^S, π^S on ℝ^{m×S}_{≥0} with values in X(S) → total functions on ℝ^{m×S}, with feasibility a separate predicate on nonnegative reports; reason: a family on the orthant extends to such a total function, and the hypotheses read nonnegative reports only
--   - encoding: ℝ^D with D = m|J| → report matrices Fin m → J → ℝ, identified with Fin (m|J|) → ℝ by ofCoords in the order of p.40; reason: the same space with the same Lebesgue measure
-- source:
--   Wang, Xu, Zhang, Tight Analysis of Randomized Truthful Scheduling: An (m+1)/2 Lower Bound, arXiv:2611.05142 (artifact sha256 a89db2da…), Lemma 5.12, p.32; App. A.2, pp.40–41

import Mathlib
import Definitions.Def_TIESched_PaddingInvariant
import Definitions.Def_TIESched_utilityInteraction
import Definitions.Def_TIESched_SatisfiesVanishingHyps
import Definitions.Def_TIESched_IsCompatibleIntegration
import Definitions.Def_TIESched_convL

set_option autoImplicit false

open MeasureTheory

namespace TIESched

/-- **Lemma 5.12** (Wang, Xu, Zhang, arXiv:2611.05142, Lemma 5.12, p.32, with `∗_L` read through
display (10), App. A.2, pp.40–41). Let `(x, u)` be a padding-invariant truthful fractional mechanism
family. Fix `|J| ≥ m`, set `D = m|J|`, and let `κ : ℝ^D → ℝ` be nonnegative and smooth, with
integral one and compact support contained in `(0, ∞)^D`. For the zero-extended utility interactions
of `(x, u)`, the left convolutions `V^J_i ∗_L κ` satisfy all the hypotheses of Lemma 5.8.
Consequently, `(V^J_i ∗_L κ)(p) = 0` for all `i ∈ [m]` and all `p ∈ ℝ^D`.

**Formalization Note.** The left convolution is `(f ∗_L κ)(p) = I_D(s ↦ f(s)κ(p − s))` for an
arbitrary compatible positive integration `I` (Lemma A.1), as App. A.2 prescribes ("the proof of
Lemma 5.12 still applies"); no Lebesgue integral of the possibly non-measurable interactions is
taken. The kernel's integral is the Lebesgue integral of the smooth `κ`. -/
theorem lemma_5_12 (m : ℕ) [NeZero m] (hm : 2 ≤ m) (I : (D : ℕ) → ((Fin D → ℝ) → ℝ) → ℝ)
    (hI : IsCompatibleIntegration I) (M : FracMech m) (hfeas : Feasible M.alloc)
    (htr : Truthful M) (hpad : PaddingInvariant M) (J : Finset ℕ) (hJ : m ≤ J.card)
    (κ : (Fin m → J → ℝ) → ℝ) (hκ0 : ∀ s, 0 ≤ κ s) (hκs : ContDiff ℝ (⊤ : ℕ∞) κ)
    (hκc : HasCompactSupport κ) (hκpos : tsupport κ ⊆ {s | ∀ i j, 0 < s i j})
    (hκint : ∫ s, κ s = 1) :
    SatisfiesVanishingHyps J
        (fun i => convL I J (zeroExt (fun q => utilityInteraction M J q i)) κ) ∧
      ∀ (i : Fin m) (p : Fin m → J → ℝ),
        convL I J (zeroExt (fun q => utilityInteraction M J q i)) κ p = 0 := by sorry

end TIESched
