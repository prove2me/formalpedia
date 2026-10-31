-- Prove2me | Theorems.Thm_RobustPrefLearn_MTP_theorem_1_part_i
-- name    : RobustPrefLearn.MTP.theorem_1_part_i
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-10-30T14:24:26.006335+00:00
-- url     : https://prove2.me/theorems/425d85bc-cff8-484d-b404-008b8bf27485
-- title:
--   Theorem 1, p. 14, first inequality — E^π_f[τ] ≥ kl(δ, 1−δ)/I_*(f) for δ-accurate π (δ ≤ 1/2)
-- statement:
--   Throughout, $K\ge2$ versions and $0<p<1$. Let $\delta\in(0,\tfrac12]$. For every $\delta$-accurate admissible policy $\pi$ and every preference $f\in\mathcal M_p$,
--   $$\mathbb E^\pi_f[\tau]\ \ge\ \frac{\mathrm{kl}(\delta,1-\delta)}{I_*(f)},$$
--   where $\mathrm{kl}$ is the Bernoulli KL divergence and $I_*(f)=\sup_{\lambda\in\Delta(\mathcal S)}\inf_{\bar f\in\overline{\mathcal M}_p(f)}D_\lambda(f\|\bar f)$ is Chernoff's information.
--
--   This is the first (non-asymptotic) inequality of Theorem 1, the instance-specific change-of-measure lower bound. The second (asymptotic) statement of Theorem 1, $\liminf_{\delta\downarrow0}\mathbb E^{\pi_\delta}_f[\tau]/\log(1/\delta)\ge1/I_*(f)$, follows from it because $\mathrm{kl}(\delta,1-\delta)/\log(1/\delta)\to1$.
--
--   **Formalization Note** This is verbatim the first conjunct of the milestone `RobustPrefLearn.MTP.theorem_1`. As there, the inequality is written multiplicatively, $\mathrm{kl}(\delta,1-\delta)\le I_*(f)\cdot\mathbb E^\pi_f[\tau]$ in $[0,\infty]$, and $\delta\le\tfrac12$ is added: the printed range $\delta\in(0,1)$ makes it false for $\delta\in(\tfrac12,1)$. The hypotheses $K\ge2$ and $0<p<1$ are added as in the parent.
-- source:
--   Feng, Caldentey & Ryan, Robust Learning of Consumer Preferences, SSRN 3215614 (https://ssrn.com/abstract=3215614), p. 14, Theorem 1 (first inequality)

import Mathlib
import Definitions.Def_RobustPrefLearn_MTP_Policy

open scoped ENNReal Topology

namespace RobustPrefLearn.MTP

/-- Theorem 1, p. 14, first inequality (non-asymptotic lower bound), for `δ ∈ (0, 1/2]`: for every
`δ`-accurate policy `π` and every `f ∈ M_p`, `kl(δ, 1 - δ) ≤ I_*(f) · E^π_f[τ]` in `[0, ∞]`. -/
theorem theorem_1_part_i (K : ℕ) (hK : 2 ≤ K) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 2 → ∀ π : Policy K, IsDeltaAccurate p δ π →
      ∀ f ∈ (Mp p : Set (Pref K)),
        ENNReal.ofReal (kl δ (1 - δ)) ≤ Istar p f * expTau π f := by sorry

end RobustPrefLearn.MTP
