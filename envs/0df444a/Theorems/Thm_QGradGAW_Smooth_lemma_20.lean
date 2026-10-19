-- Prove2me | Theorems.Thm_QGradGAW_Smooth_lemma_20
-- name    : QGradGAW.Smooth.lemma_20
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:28:33.405175+00:00
-- url     : https://prove2.me/theorems/2473976c-06b0-455e-a30a-5998564452fc
-- title:
--   Lemma 20, p. 25 — if |f(x) − g·x − c| ≤ 1/(42πN) off a 1/1000 fraction of G_nᵈ, Algorithm 2 gives Pr[|k_i − g_i| > 4/N] ≤ 1/3
-- statement:
--   Let $N=2^n$, $c\in\mathbb R$ and $g\in\mathbb R^d$ with $\|g\|_\infty\le 1/3$. Let $f:G_n^d\to\mathbb R$ satisfy
--   $$|f(x)-g\cdot x-c|\le\frac{1}{42\pi N}$$
--   for all but a $1/1000$ fraction of the points $x\in G_n^d$. Run Algorithm 2 (Jordan's algorithm: Hadamard on every qubit, the phase oracle $|x\rangle\mapsto e^{2\pi i N f(x)}|x\rangle$, the inverse grid Fourier transform on each register, measurement) and let $(k_1,\dots,k_d)\in G_n^d$ be the outcome. Then for every coordinate $i\in[d]$
--   $$\Pr\big[\,|k_i-g_i|>4/N\,\big]\;\le\;\tfrac13 .$$
--
--   A single run of Jordan's algorithm thus recovers each coordinate of the gradient of an almost-affine function to accuracy $4/N$ with constant probability; Theorem 21 amplifies this by repetition.
--
--   **Formalization Note** $f$ is a function on $\mathbb R^d$ of which only the values on the grid matter. "All but a $1/1000$ fraction" is: the number of grid labels where the inequality fails is at most $N^d/1000$. The state before measurement is the published `QAlgorithms.gradientAlgState d n f`, and the probability of the event is `QAlgorithms.probEvent`. Nannicini's Proposition 5.6 on the platform (`QAlgorithms.Nannicini.gradientAlg_approxLinear`) concerns the same algorithm with different constants and is a different statement.
-- source:
--   Gilyén, Arunachalam, Wiebe, Optimizing quantum optimization algorithms via faster quantum gradient computation, arXiv:1711.00465v3, p. 25, Lemma 20, display (21)

import Mathlib
import Definitions.Def_QGradGAW_Smooth_Setting

namespace QGradGAW.Smooth

open QAlgorithms

/-- arXiv:1711.00465v3, p. 25, Lemma 20: let `N = 2^n`, `c ∈ ℝ`, `g ∈ ℝ^d` with `‖g‖∞ ≤ 1/3`.
If `|f(x) − g · x − c| ≤ 1/(42πN)` for all but a `1/1000` fraction of the points `x ∈ G_n^d`,
then the output `(k_1, …, k_d) ∈ G_n^d` of Algorithm 2 (run on `f`) satisfies
`Pr[|k_i − g_i| > 4/N] ≤ 1/3` for every `i ∈ [d]`. -/
theorem lemma_20 (n d : ℕ) (c : ℝ) (g : Fin d → ℝ) (hg : ‖g‖ ≤ 1 / 3)
    (f : (Fin d → ℝ) → ℝ)
    (hf : ((Finset.univ.filter fun x : Fin d → Qubits n =>
        ¬ |f (gridVec x) - ∑ i, g i * gridVec x i - c| ≤ 1 / (42 * Real.pi * 2 ^ n)).card : ℝ) ≤
      (2 ^ n : ℝ) ^ d / 1000) :
    ∀ i : Fin d, probEvent (gradientAlgState d n f)
      (fun k => 4 / 2 ^ n < |gridPoint n (k i) - g i|) ≤ 1 / 3 := by sorry

end QGradGAW.Smooth
