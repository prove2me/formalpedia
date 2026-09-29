-- Prove2me | Theorems.Thm_TongString_casimir_cutoff_sum
-- name    : TongString.casimir_cutoff_sum
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-25T20:16:27.195358+00:00
-- url     : https://prove2.me/theorems/dc97380a-0673-4ee1-b134-8c4b909018db
-- title:
--   $\sum_{n\ge1}ne^{-\epsilon n}=\frac1{\epsilon^2}-\frac1{12}+O(\epsilon)$
-- statement:
--   As $\epsilon\to0^+$,
--
--   $$
--   \sum_{n=1}^{\infty} n\,e^{-\epsilon n}=\frac{1}{\epsilon^{2}}-\frac{1}{12}+O(\epsilon).
--   $$
--
--   That is, there are constants $K,\delta>0$ such that $\bigl|\sum_{n\ge1}ne^{-\epsilon n}-\epsilon^{-2}+\tfrac1{12}\bigr|\le K\epsilon$ for all $0<\epsilon<\delta$. After discarding the divergent $1/\epsilon^2$ term, this is Tong's cut-off derivation of "$\sum_{n\ge1}n=-\frac1{12}$".
--
--   **Formalization Note** The sum is over $n\in\mathbb N$ including $n=0$, whose term is $0$; the big-O is along the filter of right neighbourhoods of $0$.
-- source:
--   D. Tong, *String Theory*, University of Cambridge Part III Mathematical Tripos lecture notes (January 2009), http://www.damtp.cam.ac.uk/user/tong/string.html, Section 2.2.2 'The Casimir Energy', p. 39 (display ending '= 1/ε² − 1/12 + O(ε)')

import Mathlib

namespace TongString

open Filter Topology Asymptotics

theorem casimir_cutoff_sum :
    (fun ε : ℝ => (∑' n : ℕ, (n : ℝ) * Real.exp (-ε * n)) - (1 / ε ^ 2 - 1 / 12))
      =O[𝓝[>] 0] (fun ε : ℝ => ε) := by sorry

end TongString
