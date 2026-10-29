-- Prove2me | Theorems.Thm_PochetWolsey_Modes_single_changeover_hull
-- name    : PochetWolsey.Modes.single_changeover_hull
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T02:29:04.753693+00:00
-- url     : https://prove2.me/theorems/6fb6dbba-d314-48bf-abc5-c4bc46b6da09
-- title:
--   Proposition 12.3 — single-setup changeover hull
-- statement:
--   Let $Y^{M1-SQ}$ be the binary setup/changeover set with one label active in every period and each changeover indicating the simultaneous activity of its adjacent endpoint labels. Let $P_{\mathrm{flow}}$ be the unit flow system (12.1)–(12.4), with real coordinates in $[0,1]$. Then
--   $$\operatorname{conv}(Y^{M1-SQ})=P_{\mathrm{flow}}.$$
--   This identifies the complete fractional hull in the setup and changeover coordinates, with idle included as an ordinary label.
--
--   **Formalization Note** The graph has $n+1$ periods $0,\ldots,n$ and $n$ internal transitions. A transition index $t$ connects periods $t$ and $t+1$ and stores the book’s changeover or startup at the latter period. No transition into the first period is recorded, consistently with (12.2)–(12.3), which apply only from the second period onward. There are $m+1$ labels including idle label $0$.
-- source:
--   Pochet and Wolsey, Production Planning by Mixed Integer Programming, Springer 2006, p. 377 (PDF 388), Proposition 12.3

import Mathlib

namespace PochetWolsey.Modes

theorem single_changeover_hull (m n : ℕ) :
    convexHull ℝ ({p : (Fin (m + 1) → Fin (n + 1) → ℝ) × (Fin (m + 1) → Fin (m + 1) → Fin n → ℝ) | (∀ i, (∀ t, p.1 i t = 0 ∨ p.1 i t = 1)) ∧ (∀ i j, (∀ t, p.2 i j t = 0 ∨ p.2 i j t = 1)) ∧
    (∀ t, ∑ i, p.1 i t = 1) ∧
    (∀ i j t, p.2 i j t ≥ p.1 i t.castSucc + p.1 j t.succ - 1 ∧
      p.2 i j t ≤ p.1 i t.castSucc ∧ p.2 i j t ≤ p.1 j t.succ)}) =
    {p | (∀ i, (∀ t, 0 ≤ p.1 i t ∧ p.1 i t ≤ 1)) ∧ (∀ i j, (∀ t, 0 ≤ p.2 i j t ∧ p.2 i j t ≤ 1)) ∧
    (∑ i, p.1 i 0 = 1) ∧
    (∀ i t, p.1 i t.castSucc = ∑ j, p.2 i j t) ∧
    (∀ j t, ∑ i, p.2 i j t = p.1 j t.succ)} := by sorry

end PochetWolsey.Modes
