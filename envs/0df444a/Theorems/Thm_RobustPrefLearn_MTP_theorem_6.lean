-- Prove2me | Theorems.Thm_RobustPrefLearn_MTP_theorem_6
-- name    : RobustPrefLearn.MTP.theorem_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:38:00.56348+00:00
-- url     : https://prove2.me/theorems/ed0b6da8-5c14-4c93-868c-22c0672b19d9
-- title:
--   Theorem 6, p. 20, first sentence and (10) — MTP: E_f[τ] < ∞ and limsup E_f[τ]/log(1/δ) ≤ 1/I^OA_*; the equality clause is not formalized (false as printed for small β)
-- statement:
--   Throughout, $K\ge2$ versions and $0<p<1$. Let $C_0$ be a constant and $\beta(\delta)$ thresholds with $0<\beta(\delta)\le C_0+\log(1/\delta)$ for $\delta\in(0,1)$. For every initial display set $S_1$ and every $f\in\mathcal M_p$, the Myopic Tracking Policy with threshold $\beta(\delta)$ satisfies $\mathbb E_f[\tau]<\infty$ for every $\delta\in(0,1)$, and
--   $$\limsup_{\delta\downarrow0}\frac{\mathbb E_f[\tau]}{\log(1/\delta)}\le\frac1{I^{\mathrm{OA}}_*}. \tag{10}$$
--
--   This is the upper half of Theorem 5: MTP attains the worst-case lower bound.
--
--   **Formalization Note** The theorem's last sentence ("the inequality can be replaced by an equality when $f\in\mathcal M^{\mathrm{OA}}_p$") is not formalized: with $\beta\equiv1$ the hypothesis holds with $C_0=1$, $\mathbb E_f[\tau]$ is then a finite constant, and the ratio tends to $0$. "For every $\delta>0$" is read as $\delta\in(0,1)$, and Algorithm 1's input condition $\beta>0$ is a hypothesis. The initial set $S_1$ is arbitrary. The hypotheses $K\ge2$ ("$K\ge2$ available alternatives", §3) and $0<p<1$ are added: Definition 1 allows $p=0$, but then $\mathcal M_0$ is empty and $\log(1/p)$ is undefined.
-- source:
--   Feng, Caldentey & Ryan, Robust Learning of Consumer Preferences, SSRN 3215614 (https://ssrn.com/abstract=3215614), p. 20, Theorem 6, (10)

import Mathlib
import Definitions.Def_RobustPrefLearn_MTP_Mtp

open scoped ENNReal Topology

namespace RobustPrefLearn.MTP

/-- Theorem 6, p. 20, first sentence and (10). For any constant `C₀` and thresholds `β(δ) > 0`
with `β(δ) ≤ C₀ + log(1/δ)`, any initial display set `S₁` and any `f ∈ M_p`, the Myopic Tracking
Policy has `E_f[τ] < ∞` for every `δ ∈ (0, 1)`, and
`limsup_{δ ↓ 0} E_f[τ]/log(1/δ) ≤ 1/I^OA_*`. -/
theorem theorem_6 (K : ℕ) [NeZero K] (hK : 2 ≤ K) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (C0 : ℝ) (β : ℝ → ℝ)
    (hβ : ∀ δ ∈ Set.Ioo (0 : ℝ) 1, 0 < β δ ∧ β δ ≤ C0 + Real.log (1 / δ))
    (S1 : DS K) (f : Pref K) (hf : f ∈ (Mp p : Set (Pref K))) :
    (∀ δ ∈ Set.Ioo (0 : ℝ) 1, expTau (mtp p S1 (β δ)) f < ⊤) ∧
    Filter.limsup (fun δ : ℝ => expTau (mtp p S1 (β δ)) f / ENNReal.ofReal (Real.log (1 / δ)))
        (𝓝[>] 0) ≤ (IOA (K := K) p)⁻¹ := by sorry

end RobustPrefLearn.MTP
