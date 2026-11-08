-- Prove2me | Theorems.Thm_PureDPQR_lemma_17
-- name    : PureDPQR.lemma_17
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:59:24.560398+00:00
-- url     : https://prove2.me/theorems/9d69a846-3d84-4b17-bb01-c8533f2767bc
-- title:
--   Lemma 17, p.19 — the SelectMW transcript law is positive, $C^\infty$, with $|\partial_{v_j}\log p_v(y)|\le2\lambda T$ and $\partial^2_{v_j}\log p_v(y)\ge-T\lambda^2$
-- statement:
--   **Lemma 17** (Curvature and first-derivative bounds). Let $p_v(y)$ be the transcript law of Algorithm 1 with public $N,T\ge1$, $\lambda>0$, $0<\rho\le\frac12$ and a signed list $s_1,\dots,s_K$ with entries in $[-1,1]$. For every $v\in\mathbb R^d$, $j\in[d]$ and $y\in[K]^T$, $p_v(y)>0$, the map $v\mapsto p_v(y)$ is infinitely differentiable on $\mathbb R^d$, and
--
--   $$\big|\partial_{v_j}\log p_v(y)\big|\le2\lambda T,\qquad \partial^2_{v_j}\log p_v(y)\ge-T\lambda^2 .$$
--
--   The curvature bound is the hypothesis (4.4) of Lemma 14 with $r=\lambda\sqrt T$.
--
--   **Formalization Note** $\partial_{v_j}$ and $\partial^2_{v_j}$ are the first and second derivatives of the one-variable slice $x\mapsto\log p_{v+(x-v_j)e_j}(y)$ at $x=v_j$.
--
--   Differences from the source:
--   - generalization: the signed list s_{2i−1} = q_i, s_{2i} = −q_i of a table in [0,1]^{k×d} → any s : Fin K → Fin d → ℝ with |s_a(j)| ≤ 1; reason: the proof uses only s_a(j) ∈ [−1, 1] (p.20); the signed list of a table in [0,1] is such an s
--   - encoding: ∂_{v_j}, ∂²_{v_j}; infinitely differentiable → derivatives of the slice x ↦ log p(update v j x)(y) at v_j; ContDiff ℝ ∞; reason: coordinate partial derivatives; same quantities
--   - encoding: 1-based labels, coordinates and rounds → Fin K, Fin d, Fin T; reason: Lean convention
-- source:
--   Zou, Pure Differentially Private Query Release via Laplace Input Smoothing, arXiv:2611.04721 (held version, sha256 69b70d59…), Lemma 17, p.19 (PDF p.20); Algorithm 1, p.19

import Mathlib
import Definitions.Def_PureDPQR_transcriptProb

open scoped ContDiff

namespace PureDPQR

/-- **Lemma 17** (Curvature and first-derivative bounds), p.19 (PDF p.20).

Z. Zou, *Pure Differentially Private Query Release via Laplace Input Smoothing*, arXiv:2611.04721
(held version, sha256 69b70d59…).

"For every v ∈ R^d, j ∈ [d], and y ∈ [K]^T, the probability p_v(y) is positive, infinitely
differentiable, and |∂_{v_j} log p_v(y)| ≤ 2λT, ∂²_{v_j} log p_v(y) ≥ −Tλ². (5.3)"

Here `p_v(y)` is the transcript law of Algorithm 1 (p.19) under its Require line: public
`N, T ∈ ℕ_{≥1}`, `λ > 0`, `0 < ρ ≤ 1/2`, and the signed list `s_1, …, s_K`.

**Formalization Note.**
* The signed list is any `s : Fin K → Fin d → ℝ` with entries in `[−1, 1]` (the property the proof
  uses, p.20); the signed list of a query table in `[0,1]^{k×d}` is one (a generalization).
* "Infinitely differentiable" is `ContDiff ℝ ∞` of `v ↦ p_v(y)` on `ℝ^d`.
* `∂_{v_j}` and `∂²_{v_j}` are the first and second derivatives of the slice
  `x ↦ log p_{update v j x}(y)` at `x = v_j`. `λ` is written `lam`; indices are 0-based. -/
theorem lemma_17 {K d T : ℕ} (N : ℕ) (lam ρ : ℝ) (s : Fin K → Fin d → ℝ)
    (hN : 1 ≤ N) (hT : 1 ≤ T) (hlam : 0 < lam) (hρ : 0 < ρ) (hρ' : ρ ≤ 1 / 2)
    (hs : ∀ a j, |s a j| ≤ 1) (v : Fin d → ℝ) (j : Fin d) (y : Fin T → Fin K) :
    0 < transcriptProb N lam ρ s v y ∧
      ContDiff ℝ ∞ (fun w => transcriptProb N lam ρ s w y) ∧
      |deriv (fun x => Real.log (transcriptProb N lam ρ s (Function.update v j x) y)) (v j)| ≤
        2 * lam * T ∧
      -((T : ℝ) * lam ^ 2) ≤
        deriv^[2] (fun x => Real.log (transcriptProb N lam ρ s (Function.update v j x) y))
          (v j) := by sorry

end PureDPQR
