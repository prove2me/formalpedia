-- Prove2me | Theorems.Thm_TopkisRation_TimeMono_eq_12
-- name    : TopkisRation.TimeMono.eq_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:47:57.132998+00:00
-- url     : https://prove2.me/theorems/6bfa0e46-d7eb-47f6-89a1-e021d9b39456
-- title:
--   (12), p. 170 — difference-quotient bounds for f_t when a_t = 1 or b = 0, for small ε > 0 and any d_t ≥ 0
-- statement:
--   Consider the $n$-class rationing model with the standing assumptions (A)–(C), the optimal cost $f_t(z,B)$ of the last $t$ intervals given stock $z$ and total demand $B$ at the start of interval $t$, and the expected optimal cost $g_{t-1}$ of the following intervals. Let $1 \le t \le k$, suppose $a_i \in \{0,1\}$ for every $1 \le i \le t$, and let $z \ge 0$ and $b \ge 0$ with either $a_t = 1$ or $b = 0$. Then there is $\varepsilon_0 > 0$ such that for every $\varepsilon \in (0, \varepsilon_0)$ and every demand vector $d \ge 0$,
--   $$
--   \frac{f_t(z+\varepsilon, b+d) - f_t(z, b+d)}{\varepsilon} \le \frac{f_t(z+\varepsilon, b) - f_t(z, b)}{\varepsilon} \le \frac{h_t(z+\varepsilon) - h_t(z) + g_{t-1}(z+\varepsilon, b) - g_{t-1}(z, b)}{\varepsilon}.
--   $$
--
--   This is display (12) in the proof of Lemma 7: taking expectations over $d = d_t$ and letting $\varepsilon \downarrow 0$ yields Lemma 7. The first inequality is Lemma 5 with $f_t$ in place of $g_t$ (in difference-quotient form); the second compares interval $t$ with interval $t-1$.
--
--   **Formalization Note.** "For small enough $\varepsilon > 0$ and any $d_t \ge 0$" is read with $\varepsilon_0$ chosen before $d$ (an `∀ᶠ ε in 𝓝[>] 0` outside the quantifier over $d$), the stronger of the two readings. The hypothesis on $a_i$ for $i \le t$ is Lemma 7's, in whose proof the display appears.
-- source:
--   Topkis, Optimal ordering and rationing policies in a nonstationary dynamic inventory model with n demand classes, Management Science 15 (1968), p. 170, (12) (proof of Lemma 7)

import Mathlib
import Definitions.Def_TopkisRation_TimeMono_Model

namespace TopkisRation.TimeMono

open Filter Topology

theorem eq_12 {n : ℕ} (M : Model n) (hM : M.Standing) (t : ℕ) (ht1 : 1 ≤ t) (htk : t ≤ M.k)
    (ha : ∀ i ∈ Finset.Icc 1 t, M.a i = 0 ∨ M.a i = 1)
    (z : ℝ) (hz : 0 ≤ z) (b : Fin n → ℝ) (hb : 0 ≤ b) (hcase : M.a t = 1 ∨ b = 0) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ d : Fin n → ℝ, 0 ≤ d →
      (M.f t (z + ε) (b + d) - M.f t z (b + d)) / ε ≤ (M.f t (z + ε) b - M.f t z b) / ε ∧
      (M.f t (z + ε) b - M.f t z b) / ε ≤
        (M.h t (z + ε) - M.h t z + M.g (t - 1) (z + ε) b - M.g (t - 1) z b) / ε := by sorry

end TopkisRation.TimeMono
