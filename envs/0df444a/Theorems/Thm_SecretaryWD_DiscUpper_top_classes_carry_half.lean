-- Prove2me | Theorems.Thm_SecretaryWD_DiscUpper_top_classes_carry_half
-- name    : SecretaryWD.DiscUpper.top_classes_carry_half
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T05:59:50.388664+00:00
-- url     : https://prove2.me/theorems/62e12681-c5df-4396-bd61-85f3ad3f656a
-- title:
--   Proof of Thm 4.4 — the top $3\lceil\log_2 n\rceil+1$ discount classes carry half of $\mathbb E[\mathsf{OPT}]$
-- statement:
--   In the discounted secretary problem with $n\ge1$ elements, values $v\ge0$ and discounts $d\ge0$, let $L=\lceil\log_2 n\rceil$. Then
--   $$\sum_{c=1}^{3L+1}\mathsf{OPT}_c\;\ge\;\frac{\mathbb E_\pi[\mathsf{OPT}]}{2},$$
--   equivalently the tail $\sum_{c\ge 3L+2}\mathsf{OPT}_c$ is at most $\mathbb E_\pi[\mathsf{OPT}]/2$.
--
--   The offline optimum thus gets at least half its expected value from the top $O(\log n)$ discount scales, which is why the algorithm restricts its random class to $\{1,\dots,3L+2\}$.
--
--   **Formalization Note.** The paper writes the range as $c\le 3\log n+1$; the logarithm is base $2$ and is rounded up, $L=$ `Nat.clog 2 n`, the same convention as the algorithm's $M=3L+2$. The statement is the page's: the sum runs to $3L+1$, not to $M$.
-- source:
--   Babaioff, Dinitz, Gupta, Immorlica and Talwar, Secretary Problems: Weights and Discounts, SODA 2009 (authors' version), p. 7, proof of Theorem 4.4 ("It follows that Σ_{c≥3 log n+2} OPTc ≤ OPT/2, so that Σ_{c=1}^{3 log n+1} OPTc ≥ OPT/2")

import Mathlib
import Definitions.Def_SecretaryWD_DiscUpper_DiscountedModel

namespace SecretaryWD.DiscUpper
theorem top_classes_carry_half (n : ℕ) (hn : 1 ≤ n) (d v : Fin n → ℝ)
    (hd : ∀ t, 0 ≤ d t) (hv : ∀ e, 0 ≤ v e) :
    expectedOpt d v / 2 ≤ ∑ c ∈ Finset.Icc 1 (3 * Nat.clog 2 n + 1), optClass d v c := by sorry
end SecretaryWD.DiscUpper
