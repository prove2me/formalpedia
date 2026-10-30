-- Prove2me | Theorems.Thm_TopkisRation_FullTime_lemma_7_generalized
-- name    : TopkisRation.FullTime.lemma_7_generalized
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T14:39:55.330955+00:00
-- url     : https://prove2.me/theorems/a8e9c8c3-1f8b-4b9c-a439-03aa1887d52b
-- title:
--   Lemma 7 — full binary branch and zero-backlog extension to arbitrary earlier factors
-- statement:
--   Consider the single-procurement model of §1 under assumptions (A)–(C), with $n\ge1$ demand classes and $k$ intervals indexed backward. Demand in each interval has an arbitrary joint nonnegative law with finite coordinate means, independent of other intervals. Let $a_i\ge0$ be its backlog factors, $h_i$ its holding costs, and $g_i(z,b)$ the expected optimal remaining cost computed by (1), with terminal value $g_0(z,b)=v_1(z)+v_2(z-\sum_j b^j)$.
--
--   Fix $1\le t\le k$, stock $z\ge0$, and backlog $b\ge0$. Suppose that either
--
--   1. $a_i\in\{0,1\}$ for every $1\le i\le t$ and either $a_t=1$ or $b=0$; or
--   2. $a_t=0$ and $b=0$, with no binary restriction on earlier $a_i$.
--
--   Then the complete marginal comparison of Lemma 7 holds:
--
--   $$
--   D_z^+g_t(z,b)\le D^+h_t(z)+D_z^+g_{t-1}(z,b).
--   $$
--
--   The first branch preserves the whole printed lemma. The second is an explicit extension, including fractional factors and factors greater than one in earlier intervals. It supplies the comparison in the scope of printed Theorem 2, whose statement only fixes the adjacent two backlog factors. The original Open Lemma 7 remains a separate canonical reference.
--
--   **Formalization Note.** The functions are the recursively computed TimeMono values, not parameters assumed to have the conclusion. Extended right derivatives include $-\infty$ at $z=0$; convexity and finite values exclude $+\infty$ at every finite stock. Their sum therefore has no indeterminate $+\infty+(-\infty)$ case. Procurement assumption (D) is unnecessary for this comparison.
--
--   Differences from the source:
--   - generalization: Lemma 7 assumes binary backlog factors in every interval and either a_t=1 or b=0 → Either binary factors for 1 through t with a_t=1 or b=0, or a_t=0 and b=0 with all earlier factors arbitrary nonnegative reals; reason: The first branch contains the entire printed lemma and only removes unused future factors; the second adds the zero-current-backlog regime needed for full Theorem 2
--   - generalization: Section 1 also imposes the procurement assumption (D) on c → No condition on the unused ordering cost c; reason: The rationing values and critical levels do not use c; (D) ensures procurement attainment only
--   - encoding: Classes 1 through n and valid backward interval indices → Classes Fin n with paper class j represented by j-1; natural interval indices with explicit bounds; reason: The same finite classes and intervals are represented; subtraction t-1 is used only for t at least 1
--   - encoding: Right derivatives on the nonnegative stock half-line → The canonical EReal right liminf of positive difference quotients, including stock zero; reason: For these convex continuous functions it is the right derivative, allowing minus infinity at the boundary
-- source:
--   Topkis, Management Science 15(3) (1968), DOI 10.1287/mnsc.15.3.160, Lemma 7, p. 169 (PDF 11), with explicit domain extension; proof continues through (12), p. 170 (PDF 12)

import Mathlib
import Definitions.Def_TopkisRation_FullTime_ModelBridge

set_option autoImplicit false

namespace TopkisRation.FullTime

theorem lemma_7_generalized {n : ℕ} (hn : 0 < n)
    (M : TopkisRation.TimeMono.Model n) (hM : M.Standing)
    (t : ℕ) (ht1 : 1 ≤ t) (htk : t ≤ M.k)
    (z : ℝ) (hz : 0 ≤ z) (b : Fin n → ℝ) (hb : 0 ≤ b)
    (hcase :
      ((∀ i ∈ Finset.Icc 1 t, M.a i = 0 ∨ M.a i = 1) ∧ (M.a t = 1 ∨ b = 0)) ∨
      (M.a t = 0 ∧ b = 0)) :
    TopkisRation.Levels.rightDeriv (fun x => M.g t x b) z ≤
      TopkisRation.Levels.rightDeriv (M.h t) z +
        TopkisRation.Levels.rightDeriv (fun x => M.g (t - 1) x b) z := by sorry

end TopkisRation.FullTime
