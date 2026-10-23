-- Prove2me | Theorems.Thm_RobustPrefLearn_MTP_theorem_1
-- name    : RobustPrefLearn.MTP.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:38:10.82371+00:00
-- url     : https://prove2.me/theorems/14d955d6-6e17-4aaa-a764-4de9d50e431f
-- title:
--   Theorem 1, p. 14 — lower bound E[τ] ≥ kl(δ,1−δ)/I_*(f) (for δ ≤ 1/2) and liminf E[τ]/log(1/δ) ≥ 1/I_*(f)
-- statement:
--   Throughout, $K\ge2$ versions and $0<p<1$.
--
--   1. For every $\delta\in(0,\tfrac12]$, every $\delta$-accurate policy $\pi$ and every $f\in\mathcal M_p$,
--   $$\mathbb E^\pi_f[\tau]\ \ge\ \frac{\mathrm{kl}(\delta,1-\delta)}{I_*(f)} .$$
--   2. For every accurate family $\{\pi_\delta\}$ and every $f\in\mathcal M_p$,
--   $$\liminf_{\delta\downarrow0}\frac{\mathbb E^{\pi_\delta}_f[\tau]}{\log(1/\delta)}\ \ge\ \frac1{I_*(f)} .$$
--
--   This is the instance-specific lower bound on the number of votes any accurate policy needs; with Theorem 3 it gives the lower half of Theorem 5.
--
--   **Formalization Note** The paper states part 1 for $\delta\in(0,1)$; it is false for $\delta\in(\tfrac12,1)$ (for $K=2$, $p=\tfrac12$, the policy "show $\{1,2\}$ once and select the vote" is $0.99$-accurate with $\mathbb E[\tau]=1$, while $\mathrm{kl}(0.99,0.01)/I_*(f)\approx19.5$), so $\delta\le\tfrac12$ is added. Part 1 is written as $\mathrm{kl}(\delta,1-\delta)\le I_*(f)\cdot\mathbb E^\pi_f[\tau]$ in $[0,\infty]$, avoiding division. The hypotheses $K\ge2$ ("$K\ge2$ available alternatives", §3) and $0<p<1$ are added: Definition 1 allows $p=0$, but then $\mathcal M_0$ is empty and $\log(1/p)$ is undefined.
-- source:
--   Feng, Caldentey & Ryan, Robust Learning of Consumer Preferences, SSRN 3215614 (https://ssrn.com/abstract=3215614), p. 14, Theorem 1 and kl

import Mathlib
import Definitions.Def_RobustPrefLearn_MTP_Mtp

open scoped ENNReal Topology

namespace RobustPrefLearn.MTP

/-- Theorem 1, p. 14 (lower bound). (i) For `δ ∈ (0, 1/2]`, every `δ`-accurate policy `π` and every
`f ∈ M_p`, `E^π_f[τ] ≥ kl(δ, 1 - δ)/I_*(f)` (written multiplicatively). (ii) For every accurate
family `{π_δ}` and every `f ∈ M_p`, `liminf_{δ ↓ 0} E^{π_δ}_f[τ]/log(1/δ) ≥ 1/I_*(f)`. -/
theorem theorem_1 (K : ℕ) (hK : 2 ≤ K) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    (∀ δ : ℝ, 0 < δ → δ ≤ 1 / 2 → ∀ π : Policy K, IsDeltaAccurate p δ π →
      ∀ f ∈ (Mp p : Set (Pref K)),
        ENNReal.ofReal (kl δ (1 - δ)) ≤ Istar p f * expTau π f) ∧
    (∀ fam : ℝ → Policy K, IsAccurate p fam → ∀ f ∈ (Mp p : Set (Pref K)),
      (Istar p f)⁻¹ ≤ Filter.liminf
        (fun δ : ℝ => expTau (fam δ) f / ENNReal.ofReal (Real.log (1 / δ))) (𝓝[>] 0)) := by sorry

end RobustPrefLearn.MTP
