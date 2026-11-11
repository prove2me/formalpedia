-- Prove2me | Theorems.Thm_QVolKLS_section_4_3_bridge_bounds
-- name    : QVolKLS.section_4_3_bridge_bounds
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:36:45.637575+00:00
-- url     : https://prove2.me/theorems/18192558-81c3-4201-ae27-81462f3da3ab
-- title:
--   §4.3 — bridge identity (33) and $p_i^+\ge1/6$, $p_i^-\ge1/9$ for $c_i\in[\mu_i/2,2\mu_i]$
-- statement:
--   Let $\pi_i$ be a probability law on a finite set, $X_i>0$, $\mu_i=\mathbb E_{\pi_i}[X_i]$, $\pi_{i+1}(x)=X_i(x)\pi_i(x)/\mu_i$ (30), and suppose $\mathbb E_{\pi_i}[(X_i/\mu_i)^2]\le4$ (31). For a scale $c_i$ put
--   $$
--   p_i^+=\mathbb E_{\pi_i}\Big[\frac{X_i}{c_i+X_i}\Big],\qquad p_i^-=\mathbb E_{\pi_{i+1}}\Big[\frac{c_i}{c_i+X_i}\Big].
--   $$
--   If $c_i\in[\mu_i/2,2\mu_i]$, then
--   $$
--   p_i^-=\frac{c_i}{\mu_i}\,p_i^+,\qquad \mu_i=c_i\frac{p_i^+}{p_i^-},\qquad p_i^+\ge\frac16,\qquad p_i^-\ge\frac19 .
--   $$
--
--   These bounds let Lemma 4.1 (which needs expectations at least $1/32$) estimate each ratio $\mu_i$ of normalization constants.
--
--   Differences from the source: none.
-- source:
--   R. Zhang, Improved Upper and Lower Bounds for Quantum Convex-Body Volume Estimation, arXiv:2610.04987 (preprint, held version, sha256 eee7a45e7117af08035a8d75fd6f145fa82ddade51ad87a6507911b6a0aa4f80), §4.3, p.35, (30)–(33) and the display after 'We claim that taking c_i ∈ [µ_i/2, 2µ_i] suffices'

import Mathlib

set_option autoImplicit false

namespace QVolKLS

/-- R. Zhang, arXiv:2610.04987 (held version, sha256 eee7a45e…), **§4.3, the bridge identity (33) and
the bridge bounds**, p.35. Setting (30)–(32): `π_{i+1}(x) = X_i(x)π_i(x)/µ_i` with `µ_i = E_{π_i}[X_i]`,
`E_{π_i}[(X_i/µ_i)²] ≤ 4` (31), `Y_i^+ = X_i/(c_i + X_i)`, `p_i^+ = E_{π_i}[Y_i^+]`,
`Y_i^- = c_i/(c_i + X_i)`, `p_i^- = E_{π_{i+1}}[Y_i^-]` (32).

If `c_i ∈ [µ_i/2, 2µ_i]`, then `p_i^- = (c_i/µ_i) p_i^+` and `µ_i = c_i p_i^+/p_i^-` (33), and
`p_i^+ ≥ 1/6`, `p_i^- ≥ 1/9`.

**Formalization Note.** `π_i` (here `π`) is a probability vector on a finite type, `X_i > 0`, and
`π_{i+1}` (here `π'`) is given by (30). -/
theorem section_4_3_bridge_bounds {Ω : Type*} [Fintype Ω] (π π' X : Ω → ℝ) (c : ℝ)
    (hπ : ∀ x, 0 ≤ π x) (hπ1 : ∑ x, π x = 1) (hX : ∀ x, 0 < X x)
    (h30 : ∀ x, π' x = X x / (∑ y, π y * X y) * π x)
    (h31 : ∑ x, π x * (X x / ∑ y, π y * X y) ^ 2 ≤ 4)
    (hc : (∑ y, π y * X y) / 2 ≤ c ∧ c ≤ 2 * ∑ y, π y * X y) :
    (∑ x, π' x * (c / (c + X x))) = c / (∑ y, π y * X y) * ∑ x, π x * (X x / (c + X x)) ∧
    (∑ y, π y * X y) = c * (∑ x, π x * (X x / (c + X x))) / (∑ x, π' x * (c / (c + X x))) ∧
    1 / 6 ≤ ∑ x, π x * (X x / (c + X x)) ∧
    1 / 9 ≤ ∑ x, π' x * (c / (c + X x)) := by sorry

end QVolKLS
