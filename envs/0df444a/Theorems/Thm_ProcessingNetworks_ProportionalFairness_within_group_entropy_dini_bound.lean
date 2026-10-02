-- Prove2me | Theorems.Thm_ProcessingNetworks_ProportionalFairness_within_group_entropy_dini_bound
-- name    : ProcessingNetworks.ProportionalFairness.within_group_entropy_dini_bound
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T19:33:19.618697+00:00
-- url     : https://prove2.me/theorems/6b729144-dd01-44f0-9330-6ec5bd0e1c53
-- title:
--   Lemma 10.13 — a Dini-derivative bound on the within-group entropy term (milestone)
-- statement:
--   **Lemma 10.13.** For each $t > 0$,
--   $$D^+f(t) \le \sum_{\ell\in\mathcal L}\sum_{i\in\mathcal I(\ell):Z_i(t)>0}
--   \left(D^-Z_i(t)\log\!\frac{Z_i(t)}{Y_\ell(t)} + D^+Z_i(t) -
--   D^-Y_\ell(t)\frac{Z_i(t)}{Y_\ell(t)}\right).$$
--
--   This is the first, non-regular-point Dini-derivative bound on the within-group entropy term,
--   established before specializing to regular points in Lemma 10.14.
--
--   **Formalization note.** The sum over $i \in \mathcal I(\ell)$ for $\ell\in\mathcal L$ is
--   rendered as a sum over all $i : \mathrm{Fin}\ I$ with the bracketed term set to $0$ when
--   $Z_i(t) = 0$, equivalent since every class belongs to exactly one group under `grp`. The exact
--   bracket grouping was confirmed directly against `source.txt`/PDF p. 216 (dense plain-text
--   extraction of this display equation), per this chunk's own `BRIEF.md` pitfall note. $Z$ is
--   Lipschitz on $[0,\infty)$ (as every fluid model solution is, Section 10.5), so every Dini
--   derivative in the bound is finite and the extended-real arithmetic of the right side is the
--   ordinary one.
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 200, Lemma 10.13, Eq. (10.56)

import Mathlib
import Definitions.Def_ProcessingNetworks_ProportionalFairness_WithinGroupEntropy

namespace ProcessingNetworks.ProportionalFairness

/-- Lemma 10.13, Dai & Harrison p. 200 (PDF p. 216): for each `t > 0`, the upper-right Dini
derivative of `withinGroupEntropy` (Eq. 10.50) is bounded by, for each class `i` with `Z_i(t) > 0`,
the sum of the upper-left Dini derivative of `Z_i` times `log(Z_i(t)/Y_{grp i}(t))`, plus the
upper-right Dini derivative of `Z_i`, minus the upper-left Dini derivative of `Y_{grp i}` times
`Z_i(t)/Y_{grp i}(t)` (Eq. 10.56) — summed over all classes `i`, which is equivalent to the book's
double sum over groups `ℓ` then classes `i ∈ I(ℓ)`, since every class belongs to exactly one
group. `Z` is Lipschitz on `[0, ∞)` (as every fluid model solution is, Section 10.5), so that
all the Dini derivatives involved are finite. -/
theorem within_group_entropy_dini_bound
    {I L : ℕ} (grp : Fin I → Fin L) (Zh : ℝ → Fin I → ℝ)
    (hZnn : ∀ t, 0 ≤ t → ∀ i, 0 ≤ Zh t i)
    (hZlip : ∃ Kc : ℝ, ∀ i (s t : ℝ), 0 ≤ s → s ≤ t → |Zh t i - Zh s i| ≤ Kc * (t - s))
    (t : ℝ) (ht : 0 < t) :
    diniUpperRight (withinGroupEntropy grp Zh) t ≤
      ∑ i, if Zh t i = 0 then (0 : EReal) else
        diniUpperLeft (fun s => Zh s i) t *
            ((Real.log (Zh t i / groupAggregate grp (Zh t) (grp i)) : ℝ) : EReal) +
          diniUpperRight (fun s => Zh s i) t -
            diniUpperLeft (fun s => groupAggregate grp (Zh s) (grp i)) t *
              ((Zh t i / groupAggregate grp (Zh t) (grp i) : ℝ) : EReal) := by sorry

end ProcessingNetworks.ProportionalFairness
