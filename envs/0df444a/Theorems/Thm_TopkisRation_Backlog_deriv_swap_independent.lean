-- Prove2me | Theorems.Thm_TopkisRation_Backlog_deriv_swap_independent
-- name    : TopkisRation.Backlog.deriv_swap_independent
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:48:43.397008+00:00
-- url     : https://prove2.me/theorems/c1818cee-4d71-483c-b99b-ad9cd244b3f9
-- title:
--   Proof of Theorem 3, p. 173 — under full backlogging, D_ε⁺g_t(z, ε(δ_j − δ_s) + B) at ε = 0 is independent of B¹, …, Bʲ
-- statement:
--   Consider the inventory model of Topkis (1968, §1) under its standing assumptions, and suppose there is complete backlogging in each of the intervals $1,\dots,t$: $a_1 = \dots = a_t = 1$. Let $j < s$ be two demand classes and $z \ge 0$ a stock level. For a backlog vector $B \ge 0$ with $B^s > 0$ consider the right derivative at $\varepsilon = 0$ of the expected cost when $\varepsilon$ units of class-$s$ backlog are replaced by $\varepsilon$ units of class-$j$ backlog,
--   $$
--   D_\varepsilon^+ g_t\big(z,\ \varepsilon(\delta_j - \delta_s) + B\big)\big|_{\varepsilon = 0}.
--   $$
--   Then this quantity is independent of $B^1,\dots,B^j$: if $B' \ge 0$ agrees with $B$ in every class $i > j$, then
--   $$
--   D_\varepsilon^+ g_t\big(z,\ \varepsilon(\delta_j - \delta_s) + B\big)\big|_{\varepsilon=0} = D_\varepsilon^+ g_t\big(z,\ \varepsilon(\delta_j - \delta_s) + B'\big)\big|_{\varepsilon=0}.
--   $$
--
--   This is the analogue, for backlog swaps, of part (c) of Theorem 1, and it is the statement the proof of Theorem 3 uses to show that the marginal values of the class-$j$ critical level do not see the lower classes.
--
--   **Formalization Note** $D^+$ is the extended-real right derivative (a liminf of difference quotients as $\varepsilon \downarrow 0$). The hypothesis $B^s > 0$ keeps $\varepsilon(\delta_j - \delta_s) + B \ge 0$ for small $\varepsilon > 0$; $B'^s = B^s$ follows from the agreement hypothesis since $s > j$. Independence of the demand classes, assumed in Theorem 3, is not needed for this one-model statement and is not assumed. The page writes the second argument of $g_t$ as $B$; it is a backlog vector.
-- source:
--   Topkis, Optimal ordering and rationing policies in a nonstationary dynamic inventory model with n demand classes, Management Science 15 (1968), p. 173, §2 The Backlog Case, proof of Theorem 3 (sentence after (17))

import Mathlib
import Definitions.Def_TopkisRation_Backlog_Model

namespace TopkisRation.Backlog

variable {n : ℕ}

/-- Proof of Theorem 3, p. 173: under full backlogging in intervals 1, …, t, for classes j < s and a
backlog vector with Bˢ > 0, the right derivative at ε = 0 of ε ↦ g_t(z, ε(δ_j − δ_s) + B) does not
depend on B¹, …, Bʲ. -/
theorem deriv_swap_independent (M : Model n) (hM : M.Standing) (t : ℕ) (ht : t ≤ M.k)
    (ha : ∀ i ∈ Finset.Icc 1 t, M.a i = 1) (j s : Fin n) (hjs : j < s) :
    ∀ z, 0 ≤ z → ∀ B B' : Fin n → ℝ, 0 ≤ B → 0 ≤ B' → 0 < B s →
      (∀ i, j < i → B i = B' i) →
      TopkisRation.Levels.rightDeriv (fun ε => M.g t z (ε • (Pi.single j 1 - Pi.single s 1) + B)) 0 =
        TopkisRation.Levels.rightDeriv (fun ε => M.g t z (ε • (Pi.single j 1 - Pi.single s 1) + B')) 0 := by sorry

end TopkisRation.Backlog
