-- Prove2me | Theorems.Thm_ScarceIdeas_lemma_2_iii
-- name    : ScarceIdeas.lemma_2_iii
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:16:03.359026+00:00
-- url     : https://prove2.me/theorems/c3dd1d58-f8c5-41f8-953c-5082e268dc3f
-- title:
--   Lemma 2 (iii): $m_{k+1}/m_k$ strictly decreases and equals $(k+1)/\phi+o(1/\phi)$
-- statement:
--   Let $h_0$ satisfy Assumption 1 and let $k\ge1$. The ratio $\phi\mapsto m_{k+1}(\phi)/m_k(\phi)$ is strictly decreasing on $[0,\infty)$, and
--
--   $$\lim_{\phi\to\infty}\phi\,\frac{m_{k+1}(\phi)}{m_k(\phi)}=k+1,\qquad\lim_{\phi\to\infty}\frac{m_{k+1}(\phi)}{m_k(\phi)}=0 .$$
--
--   For $k=1$, $m_2/m_1=2/\phi+o(1/\phi)$: this is the source of the constant $2$ in the rate of Theorem 3.
--
--   Differences from the source:
--
--   - generalization: as ϕ → ∞, the ratio m_{k+1}/m_k is strictly decreasing → strictly decreasing on all of [0, ∞); reason: the proof (Cauchy–Schwarz, (35)–(37)) shows it at every ϕ; it implies the eventual statement
--   - encoding: m_{k+1}/m_k = (k+1)/ϕ + o(1/ϕ) → ϕ · m_{k+1}(ϕ)/m_k(ϕ) → k + 1; reason: equivalent by the definition of o(·)
-- source:
--   Basov, Erkal, Minehart, Scotchmer, Scarcity of Ideas and Optimal R&D Policy, SSRN 4628270, Lemma 2 (iii), p.20; proof pp.35–36, (35)–(38)

import Mathlib
import Definitions.Def_ScarceIdeas_Assumption1
import Definitions.Def_ScarceIdeas_moment

namespace ScarceIdeas

open Filter Topology

/-- **Lemma 2 (iii): the ratio `m_{k+1}/m_k` is strictly decreasing and equals `(k+1)/ϕ + o(1/ϕ)`.**
Basov, Erkal, Minehart, Scotchmer, *Scarcity of Ideas and Optimal R&D Policy*, SSRN 4628270,
Lemma 2 (iii), p.20; proof pp.35–36, (35)–(38).

Under Assumption 1, for every `k ≥ 1`: the ratio `ϕ ↦ m_{k+1}(ϕ)/m_k(ϕ)` is strictly decreasing
on `[0, ∞)`, and

$$\lim_{\phi\to\infty}\phi\,\frac{m_{k+1}(\phi)}{m_k(\phi)}=k+1,\qquad
\lim_{\phi\to\infty}\frac{m_{k+1}(\phi)}{m_k(\phi)}=0 .$$

**Formalization Note** The page's "As ϕ → ∞, the ratio … is strictly decreasing" is stated on
all of `[0, ∞)`, which the proof (Cauchy–Schwarz, (35)–(37)) establishes and which implies the
eventual statement. `(k+1)/ϕ + o(1/ϕ)` is stated as `ϕ · ratio → k + 1`. -/
theorem lemma_2_iii (h0 : ℝ → ℝ) (h0A : Assumption1 h0) (k : ℕ) (hk : 1 ≤ k) :
    StrictAntiOn (fun ϕ => moment h0 (k + 1) ϕ / moment h0 k ϕ) (Set.Ici 0) ∧
    Tendsto (fun ϕ : ℝ => ϕ * (moment h0 (k + 1) ϕ / moment h0 k ϕ)) atTop
      (𝓝 ((k : ℝ) + 1)) ∧
    Tendsto (fun ϕ => moment h0 (k + 1) ϕ / moment h0 k ϕ) atTop (𝓝 0) := by sorry

end ScarceIdeas
