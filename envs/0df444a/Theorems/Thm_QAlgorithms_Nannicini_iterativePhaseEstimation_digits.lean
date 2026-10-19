-- Prove2me | Theorems.Thm_QAlgorithms_Nannicini_iterativePhaseEstimation_digits
-- name    : QAlgorithms.Nannicini.iterativePhaseEstimation_digits
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-13T17:44:12.086159+00:00
-- url     : https://prove2.me/theorems/b0e5f377-a9db-468f-a139-1be9ea64c7ae
-- title:
--   Correctness of the digits computed by iterative phase estimation (corrected)
-- statement:
--   Let $\varphi\in[0,1)$ be a phase (in full turns), $h\in\mathbb N$ ($h=q-2$), and let $\omega_1,\dots,\omega_h$ be the angle estimates used by the iterative phase estimation algorithm of §3.3.2, $\omega_i$ being the estimate of $2^{i-1}\varphi$. The algorithm computes binary digits $p_1,\dots,p_{h+2}$ as follows: $p_hp_{h+1}p_{h+2}$ are the digits of $\omega_h$ rounded to the closest multiple of $1/8$ (modulo $1$); then for $j=h-1,\dots,1$, $p_j=0$ if $d(0.0p_{j+1}p_{j+2},\omega_j)<1/4$ and $p_j=1$ otherwise. Here $d(x,y)$ is the distance between $x$ and $y$ modulo $1$.
--
--   Fix $1\le j\le h$. If $d(\omega_i,2^{i-1}\varphi)\le 1/16$ for every step $i=h,h-1,\dots,j$, then
--
--   $$
--   d\big(0.p_jp_{j+1}\dots p_{h+2},\ 2^{j-1}\varphi\big)\ \le\ 2^{-(h+3-j)} .
--   $$
--
--   In particular, for $j=1$ the algorithm outputs $q=h+2$ binary digits of $\varphi$ with error at most $2^{-q}$ on the circle, which together with a union bound over the $h$ estimation steps gives the success guarantee of iterative phase estimation.
--
--   **Formalization Note** The page states the bound with plain absolute values and strict inequality. Both are corrected: angles are only known modulo $1$ (so all distances are on the circle), and the strict bound already fails at the base case ($\omega_h=1/16$ is equidistant from $0$ and $1/8$, and rounding gives error exactly $1/8$); the induction proves $\le$, matching the goal $\Pr(\min\{\dots\}\le 2^{-q})$ on p.66. The digits are the shared definition `ipeDigits h ω` and $0.p_j\dots p_{h+2}$ is `binFracFrom`.
-- source:
--   Giacomo Nannicini, Quantum algorithms for optimizers, 2025, v5; notes dated 9 July 2025, PDF p. 66, Proposition 3.17. https://arxiv.org/pdf/2408.07086v5

import Definitions.Def_QAlgorithms_Defs_AmplitudeEstimation
set_option autoImplicit false

namespace QAlgorithms.Nannicini

open QAlgorithms



/-- Nannicini p.66, Proposition 3.17 (correctness of iterative phase estimation), **corrected**
(trap 30, see `HARD.md`). Let `φ ∈ [0, 1)`, `h = q − 2`, and let `ω i` be the estimate of the
angle `2^{i−1} φ` (in turns) used at step `i`. The digits `p_1 … p_{h+2}` are those computed by
the algorithm of §3.3.2 (`ipeDigits h ω`: initialization rounds `ω_h` to the closest multiple of
`1/8`, giving `p_h p_{h+1} p_{h+2}`; step `j = h−1, …, 1` sets `p_j = 0` iff
`|0.0 p_{j+1} p_{j+2} − ω_j| < 1/4` on the circle). If at steps `i = h, …, j` the estimate `ω_i`
is within `1/16` of `2^{i−1} φ`, then `0.p_j … p_{h+2}` is within `2^{−(h+3−j)}` of `2^{j−1} φ`.
All distances are on the circle (angles are known modulo `1`, p.66), and the bound is `≤`
rather than the page's `<`, which already fails at the base case (`ω_h = 1/16`). -/
theorem iterativePhaseEstimation_digits (φ : ℝ) (hφ0 : 0 ≤ φ) (hφ1 : φ < 1) (h : ℕ)
    (ω : ℕ → ℝ) (j : ℕ) (hj1 : 1 ≤ j) (hjh : j ≤ h)
    (hω : ∀ i, j ≤ i → i ≤ h → circDist (ω i) ((2 : ℝ) ^ (i - 1) * φ) ≤ 1 / 16) :
    circDist (binFracFrom (ipeDigits h ω) j (h + 2)) ((2 : ℝ) ^ (j - 1) * φ) ≤
      ((2 : ℝ) ^ (h + 3 - j))⁻¹ := by sorry

end QAlgorithms.Nannicini
