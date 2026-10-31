-- Prove2me | Theorems.Thm_RobustPrefLearn_MTP_theorem_6_limsup
-- name    : RobustPrefLearn.MTP.theorem_6_limsup
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-10-30T14:50:43.448149+00:00
-- url     : https://prove2.me/theorems/61127990-699e-40ed-af04-c6a8f7ab87e6
-- title:
--   Theorem 6, p. 20, (10) — limsup_{δ↓0} E_f[τ]/log(1/δ) ≤ 1/I^OA_* under MTP
-- statement:
--   Throughout, $K\ge2$ versions and $0<p<1$. Let $C_0$ be a constant and $\beta(\delta)$ thresholds with $0<\beta(\delta)\le C_0+\log(1/\delta)$ for $\delta\in(0,1)$. For every initial display set $S_1$ and every $f\in\mathcal M_p$, the Myopic Tracking Policy with threshold $\beta(\delta)$ satisfies
--   $$\limsup_{\delta\downarrow0}\frac{\mathbb E_f[\tau]}{\log(1/\delta)}\le\frac1{I^{\mathrm{OA}}_*}, \tag{10}$$
--   where $I^{\mathrm{OA}}_*=\inf_{f\in\mathcal M_p}I_*(f)$.
--
--   This is the asymptotic upper bound (10) of Theorem 6, the part of Theorem 6 that shows MTP attains the worst-case lower bound. The other part of Theorem 6, $\mathbb E_f[\tau]<\infty$, is `RobustPrefLearn.MTP.theorem_6_finite`.
--
--   **Formalization Note** This is verbatim the second conjunct of the milestone `RobustPrefLearn.MTP.theorem_6`, with the same hypotheses; rates are in $[0,\infty]$. The equality clause for $f\in\mathcal M^{\mathrm{OA}}_p$ is not formalized, as in the parent. The hypotheses $K\ge2$ and $0<p<1$ are added as in the parent.
-- source:
--   Feng, Caldentey & Ryan, Robust Learning of Consumer Preferences, SSRN 3215614 (https://ssrn.com/abstract=3215614), p. 20, Theorem 6, inequality (10)

import Mathlib
import Definitions.Def_RobustPrefLearn_MTP_Mtp

open scoped ENNReal Topology

namespace RobustPrefLearn.MTP

/-- Theorem 6, p. 20, (10) (asymptotic sample complexity of MTP). For any constant `C₀` and
thresholds `β(δ) > 0` with `β(δ) ≤ C₀ + log(1/δ)`, any initial display set `S₁` and any `f ∈ M_p`,
`limsup_{δ ↓ 0} E_f[τ]/log(1/δ) ≤ 1/I^OA_*` under the Myopic Tracking Policy. -/
theorem theorem_6_limsup (K : ℕ) [NeZero K] (hK : 2 ≤ K) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (C0 : ℝ) (β : ℝ → ℝ)
    (hβ : ∀ δ ∈ Set.Ioo (0 : ℝ) 1, 0 < β δ ∧ β δ ≤ C0 + Real.log (1 / δ))
    (S1 : DS K) (f : Pref K) (hf : f ∈ (Mp p : Set (Pref K))) :
    Filter.limsup (fun δ : ℝ => expTau (mtp p S1 (β δ)) f / ENNReal.ofReal (Real.log (1 / δ)))
        (𝓝[>] 0) ≤ (IOA (K := K) p)⁻¹ := by sorry

end RobustPrefLearn.MTP
