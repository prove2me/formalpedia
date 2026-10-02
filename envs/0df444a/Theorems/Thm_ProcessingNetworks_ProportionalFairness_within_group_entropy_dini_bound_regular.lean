-- Prove2me | Theorems.Thm_ProcessingNetworks_ProportionalFairness_within_group_entropy_dini_bound_regular
-- name    : ProcessingNetworks.ProportionalFairness.within_group_entropy_dini_bound_regular
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T19:34:34.100986+00:00
-- url     : https://prove2.me/theorems/98f595c0-47f6-4261-9622-72f8223a679b
-- title:
--   Lemma 10.14 — the Dini-derivative bound at regular points (milestone)
-- statement:
--   **Lemma 10.14.** At each regular point $t > 0$,
--   $$D^+f(t) \le \sum_{\ell\in\mathcal L}\sum_{i\in\mathcal I(\ell):Z_i(t)>0} \dot Z_i(t)
--   \log\!\frac{Z_i(t)}{Y_\ell(t)}.$$
--
--   Specializing Lemma 10.13's bound to a regular point of $Z$ (where $D^+Z_i=D^-Z_i=\dot Z_i$),
--   the last two terms of (10.56) telescope to $0$ (Eq. 10.68), leaving exactly this bound —
--   feeding directly into Lemma 10.9's bound on $D^+\varphi$ (mission IX).
--
--   **Formalization note.** Specializing Lemma 10.13's bound to a regular point of $Z$ (where
--   $D^+Z_i=D^-Z_i=\dot Z_i$), the last two terms of (10.56) telescope to $0$ (Eq. 10.68), leaving
--   exactly this bound — feeding directly into Lemma 10.9's bound on $D^+\varphi$ (mission IX).
--   $Z$ is Lipschitz on $[0,\infty)$, as in Lemma 10.13.
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 203, Lemma 10.14, Eq. (10.66)

import Mathlib
import Definitions.Def_ProcessingNetworks_ProportionalFairness_WithinGroupEntropy

namespace ProcessingNetworks.ProportionalFairness

/-- Lemma 10.14, Dai & Harrison p. 203 (PDF p. 219): at each regular point `t > 0` of `Z`, the
upper-right Dini derivative of `withinGroupEntropy` is bounded by
`∑_i Ż_i(t) log(Z_i(t)/Y_{grp i}(t))` over classes `i` with `Z_i(t) > 0` (Eq. 10.66). -/
theorem within_group_entropy_dini_bound_regular
    {I L : ℕ} (grp : Fin I → Fin L) (Zh : ℝ → Fin I → ℝ)
    (hZnn : ∀ t, 0 ≤ t → ∀ i, 0 ≤ Zh t i)
    (hZlip : ∃ Kc : ℝ, ∀ i (s t : ℝ), 0 ≤ s → s ≤ t → |Zh t i - Zh s i| ≤ Kc * (t - s))
    (t : ℝ) (ht : 0 < t)
    (hreg : ∀ i, DifferentiableAt ℝ (fun s => Zh s i) t) :
    diniUpperRight (withinGroupEntropy grp Zh) t ≤
      ((∑ i, if Zh t i = 0 then 0 else
        deriv (fun s => Zh s i) t * Real.log (Zh t i / groupAggregate grp (Zh t) (grp i)) : ℝ) :
          EReal) := by sorry

end ProcessingNetworks.ProportionalFairness
