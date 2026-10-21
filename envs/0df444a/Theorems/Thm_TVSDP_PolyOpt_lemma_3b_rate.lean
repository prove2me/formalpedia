-- Prove2me | Theorems.Thm_TVSDP_PolyOpt_lemma_3b_rate
-- name    : TVSDP.PolyOpt.lemma_3b_rate
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T04:13:58.260065+00:00
-- url     : https://prove2.me/theorems/f2e59ade-0852-4da9-a9de-fb0f65f4a27f
-- title:
--   Proof of Lemma 3(b), p. 12 — the explicit bound $\sup_{t\in[0,1]}|a(t)\mathcal M_vx(t)-\mathcal M_v(a\cdot x)(t)|\le L\gamma/v$
-- statement:
--   Let $a\in\mathbb R[t]$, let $x:[0,1]\to\mathbb R$ be measurable, and let $L,\gamma$ be constants with $|a'(t)|\le L$ and $|x(t)|\le\gamma$ for all $t\in[0,1]$ (for instance $L=\sup_{t\in[0,1]}|a'(t)|$ and $\gamma=\sup_{t\in[0,1]}|x(t)|$). Then for every integer $v\ge1$,
--
--   $$\bigl|a(t)\,\mathcal M_vx(t)-\mathcal M_v(a\cdot x)(t)\bigr|\le\frac{L\gamma}{v}\qquad\text{for every } t\in[0,1].$$
--
--   This is the quantitative estimate the paper's proof of Lemma 3(b) establishes; Lemma 3(b) follows from it.
--
--   **Formalization Note** $L$ and $\gamma$ are arbitrary upper bounds rather than the suprema themselves, which is equivalent. The hypothesis $v\ge1$ is added because the page divides by $v$.
-- source:
--   Ahmadi & El Khadir, Time-varying semidefinite programs, arXiv:1808.03994v2, p. 12, proof of Lemma 3(b), final display

import Mathlib
import Definitions.Def_TVSDP_PolyOpt_Mollifier

namespace TVSDP.PolyOpt

/-- Proof of Lemma 3(b), p. 12: with `L ≥ sup_{t ∈ [0,1]} |a'(t)|` and `γ ≥ sup_{t ∈ [0,1]} |x(t)|`,
for every `v ≥ 1` and every `t ∈ [0,1]`, `|a(t) 𝓜_v x(t) - 𝓜_v(a · x)(t)| ≤ Lγ / v`. -/
theorem lemma_3b_rate (a : Polynomial ℝ) (x : ℝ → ℝ) (hx : Measurable x) (L γ : ℝ)
    (hL : ∀ t ∈ Set.Icc (0:ℝ) 1, |a.derivative.eval t| ≤ L)
    (hγ : ∀ t ∈ Set.Icc (0:ℝ) 1, |x t| ≤ γ) (v : ℕ) (hv : 1 ≤ v) :
    ∀ t ∈ Set.Icc (0:ℝ) 1,
      |a.eval t * Mv v x t - Mv v (fun s => a.eval s * x s) t| ≤ L * γ / v := by sorry

end TVSDP.PolyOpt
