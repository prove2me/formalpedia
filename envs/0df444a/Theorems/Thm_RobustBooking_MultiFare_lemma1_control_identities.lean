-- Prove2me | Theorems.Thm_RobustBooking_MultiFare_lemma1_control_identities
-- name    : RobustBooking.MultiFare.lemma1_control_identities
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T23:43:44.283597+00:00
-- url     : https://prove2.me/theorems/71572b5e-610c-4819-9b5b-1875b834f8d6
-- title:
--   Lemma 1 — the controls of Eqs. (7)–(9) satisfy identities (10), (11) and (12)
-- statement:
--   Let $m \ge 2$, let $f_1 > f_2 > \dots > f_m > 0$ be fares and $n > 0$ a capacity, and let $\Delta$, $\theta$ and $Q$ be defined by Eqs. (6)–(9). Then
--   $$f_i(Q_i - Q_{i+1}) = \frac{n}{\Delta}(f_i - f_{i+1}) \quad (i = 1, \dots, m-1), \qquad f_m(Q_m - Q_{m+1}) = \frac{f_m n}{\Delta},$$
--   $$\sum_{i=i'}^{m} f_i(Q_i - Q_{i+1}) = f_{i'}\,\frac{n}{\Delta} \quad (1 \le i' \le m).$$
--   Identity (12) says that when the classes $i', \dots, m$ are filled up to their controls, the revenue collected is exactly a $1/\Delta$ fraction of $n f_{i'}$, the revenue of selling all capacity at fare $f_{i'}$. It is the step Theorem 5's proof uses.
--
--   **Formalization Note.** The paper's §2.1 assumes $m \ge 3$; the identities hold, and are stated, for $m \ge 2$. Indices are 1-based natural numbers.
-- source:
--   Ball, Queyranne, Toward Robust Revenue Management: Competitive Analysis of Online Booking, Oper. Res. 57(4), 2009, p. 957, Lemma 1, Eqs. (10)–(12)

import Mathlib
import Definitions.Def_RobustBooking_MultiFare_ProtectionLevels

namespace RobustBooking.MultiFare

/-- Lemma 1 (p. 957), Eqs. (10)–(12), for fares `f 1 > f 2 > ⋯ > f m > 0`, `m ≥ 2`,
capacity `n > 0`, and `θ`, `Q` defined by Eqs. (7)–(9). -/
theorem lemma1_control_identities (m : ℕ) (f : ℕ → ℝ) (n : ℝ) (hm : 2 ≤ m)
    (hf : StrictAntiOn f (Set.Icc 1 m)) (hfm : 0 < f m) (hn : 0 < n) :
    (∀ i ∈ Finset.Icc 1 (m - 1),
        f i * (Q m f n i - Q m f n (i + 1)) = n / Delta m f * (f i - f (i + 1))) ∧
    f m * (Q m f n m - Q m f n (m + 1)) = f m * n / Delta m f ∧
    (∀ i' ∈ Finset.Icc 1 m,
        ∑ i ∈ Finset.Icc i' m, f i * (Q m f n i - Q m f n (i + 1)) = f i' * (n / Delta m f)) := by sorry

end RobustBooking.MultiFare
