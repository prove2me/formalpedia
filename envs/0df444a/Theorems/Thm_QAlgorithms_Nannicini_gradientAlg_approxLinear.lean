-- Prove2me | Theorems.Thm_QAlgorithms_Nannicini_gradientAlg_approxLinear
-- name    : QAlgorithms.Nannicini.gradientAlg_approxLinear
-- status  : Open
-- author  : @Goku
-- created : 2026-10-13T17:45:56.243654+00:00
-- url     : https://prove2.me/theorems/6cf9024a-a528-4c98-bfcb-7c9e3aa2d9db
-- title:
--   The gradient algorithm for approximately linear functions
-- statement:
--   This proposition is the gradient algorithm for approximately linear functions.
--
--   Let $q \ge 1$ and $d \ge 0$ be integers, $b \in \mathbb R$, and $g \in \mathbb R^d$ with $\|g\|_\infty \le 1/3$. Let $f : [-\tfrac12,\tfrac12]^d \to \mathbb R$. Consider the grid
--
--   $$
--   G_q = \Big\{ \tfrac{j}{2^q} - \tfrac12 + \tfrac{1}{2^{q+1}} : j = 0,\dots,2^q-1 \Big\},
--   $$
--
--   where $\hat\jmath$ denotes the grid point of the $q$-bit string $j$, and let $G_q^d$ be the $d$-fold product grid with $2^{dq}$ points. Algorithm 3 does the following:
--
--   1. It applies $H^{\otimes q}$ to each of $d$ registers of $q$ qubits in $|0\rangle$.
--   2. It applies the phase oracle $|x\rangle \mapsto e^{2\pi i 2^q f(\hat x)}|x\rangle$.
--   3. It applies the inverse $Q_{G_q}^\dagger$ of the shifted Fourier transform $Q_{G_q}|k\rangle = 2^{-q/2}\sum_j e^{2\pi i 2^q \hat\jmath \hat k}|j\rangle$ to each register.
--   4. It measures the registers and outputs $\tilde g = (\hat k_1,\dots,\hat k_d)$.
--
--   If
--
--   $$
--   |f(x) - \langle g, x\rangle - b| \le \frac{1}{20\pi 2^q}
--   $$
--
--   holds for at least $99.9\%$ of the points $x \in G_q^d$, then
--
--   $$
--   \Pr\Big(|\tilde g_j - g_j| \le \frac{1}{2^q}\Big) > \frac35 \qquad \text{for every } j = 1,\dots,d.
--   $$
--
--   The result makes the gradient algorithm robust: $f$ need only be close to linear on most grid points, for instance when $f$ is evaluated by a circuit that sometimes fails.
--
--   **Formalization Note** $f$ is taken on all of $\mathbb R^d$, because only its values on the grid enter the algorithm. The fraction condition is stated as the number of good grid points being at least $\tfrac{999}{1000}\,2^{dq}$.
-- source:
--   Giacomo Nannicini, Quantum algorithms for optimizers, 2025, v5; notes dated 9 July 2025, PDF p. 110, Proposition 5.6. https://arxiv.org/pdf/2408.07086v5

import Definitions.Def_QAlgorithms_Defs_GradientMethods
import Definitions.Def_QAlgorithms_Nannicini_Ch05a_Model
set_option autoImplicit false

namespace QAlgorithms.Nannicini


/-- Nannicini p.110, Proposition 5.6 (based on Lem. 5.1 of Gilyén et al. 2019). Let `q > 0`,
`b ∈ ℝ`, `g ∈ ℝ^d` with `‖g‖_∞ ≤ 1/3`, and `f : [−1/2, 1/2]^d → ℝ` (taken on `ℝ^d`; only its
values on the grid are used). Let `G_q = {j/2^q − 1/2 + 1/2^{q+1} : j = 0, …, 2^q − 1}` (p.109)
and `x̂` the grid point of the register contents `x`. If `|f(x̂) − ⟨g, x̂⟩ − b| ≤ 1/(20π2^q)` for at
least `99.9%` of the `2^{dq}` points `x̂ ∈ G_q^d`, then the output `g̃ = (k̂_1, …, k̂_d)` of the
gradient algorithm (Alg. 3, p.110: `H^{⊗q}` on each of `d` registers in `|0⟩`, the phase oracle
`|x⟩ ↦ e^{2πi 2^q f(x̂)}|x⟩`, `Q_{G_q}†` on each register, measure) satisfies
`Pr(|g̃_j − g_j| ≤ 1/2^q) > 3/5` for every `j = 1, …, d`. -/
theorem gradientAlg_approxLinear (d q : ℕ) (hq : 0 < q) (b : ℝ) (g : Fin d → ℝ)
    (hg : ∀ i, |g i| ≤ 1 / 3) (f : (Fin d → ℝ) → ℝ)
    (hf : (999 / 1000 : ℝ) * (2 : ℝ) ^ (d * q) ≤
      ((Finset.univ.filter fun x : Fin d → Qubits q =>
          |f (fun i => gridPoint q (x i)) - ∑ i, g i * gridPoint q (x i) - b| ≤
            1 / (20 * Real.pi * (2 : ℝ) ^ q)).card : ℝ)) :
    ∀ j : Fin d, 3 / 5 < probEvent (gradientAlgState d q f)
      fun k => |gridPoint q (k j) - g j| ≤ 1 / (2 : ℝ) ^ q := by
  sorry






end QAlgorithms.Nannicini
