-- Prove2me | Theorems.Thm_PrivLearn_MaskedParity_good_event
-- name    : PrivLearn.MaskedParity.good_event
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T06:47:40.458981+00:00
-- url     : https://prove2.me/theorems/d888c2f1-cdbb-49f5-987e-4cdf9e40914c
-- title:
--   Proof of Theorem 5.16(2), p. 30 — Pr[Good] ≥ 1 − t/2^{d/3+2}
-- statement:
--   Let $d$ be a power of two, let examples be uniform on the MASKED-PARITY domain $D$, and let $g_1,\dots,g_t$ be statistical queries with values in $\{+1,-1\}$ on labels $y\in\{+1,-1\}$. Let $(\bar r,\bar a)$ be uniform on $\{0,1\}^d\times\{0,1\}$ and let $\mathit{Good}$ be the event that $|\langle f^0_{g_k},c^0_{\bar r,\bar a}\rangle|<1/2^{d/3}$ for every $k\in[t]$. Then
--   $$\Pr[\mathit{Good}]\ge1-\frac t{2^{d/3+2}} .$$
--
--   On $\mathit{Good}$ the oracle $\mathcal O$ answers every query of tolerance at least $2^{-d/3}$ without using $\bar a$.
--
--   **Formalization Note.** The page defines $\mathit{Good}$ with $c_{\bar r,\bar a}$ and $\le$; the proof needs, and we state, $c^0_{\bar r,\bar a}$ and the strict $<$, which is the complement of the event counted on p. 30 and matches the oracle's strict test. The replacement of $c_{\bar r,\bar a}$ by $c^0_{\bar r,\bar a}$ changes nothing, since $f^0_{g}$ vanishes where $b=1$ and so $\langle f^0_g,c_{\bar r,\bar a}\rangle=\langle f^0_g,c^0_{\bar r,\bar a}\rangle$; the strict $<$ makes the event smaller, so the statement implies the printed one. The event does not depend on $\bar a$ (because $c^0_{r,1}=-c^0_{r,0}$), so the probability "taken only over $\bar r$" equals the probability over the uniform pair, which is the count divided by $2^{d+1}$ stated here. Powers $2^{d/3}$ are real powers.
-- source:
--   Kasiviswanathan, Lee, Nissim, Raskhodnikova and Smith, What Can We Learn Privately?, arXiv:0803.0924v3, p. 30, proof of Theorem 5.16 part (2), the event Good

import Mathlib
import Definitions.Def_PrivLearn_MaskedParity_Model
import Definitions.Def_PrivLearn_MaskedParity_Oracle

namespace PrivLearn.MaskedParity

/-- **`Pr[Good] ≥ 1 − t/2^{d/3+2}`** (p. 30), with the event `Good` read as
`|⟨f^0_{g_k}, c^0_{r̄,ā}⟩| < 1/2^{d/3}` for every `k` (the page prints `c_{r̄,ā}` and `≤`; see the
natural-language statement). Let `d` be a power of two and `g_1, …, g_t` statistical queries with
values `±1` on labels `±1`. If `(r̄, ā)` is uniform on `{0,1}^d × {0,1}`, then `Good` has
probability at least `1 − t/2^{d/3+2}`. -/
theorem good_event {d : ℕ} (hd : ∃ m : ℕ, d = 2 ^ m) (t : ℕ) (g : Fin t → Dom d → ℝ → ℝ)
    (hg : ∀ k u y, (y = 1 ∨ y = -1) → (g k u y = 1 ∨ g k u y = -1)) :
    1 - (t : ℝ) / (2 : ℝ) ^ ((d : ℝ) / 3 + 2) ≤
      ((Finset.univ.filter fun ra : (Fin d → ZMod 2) × ZMod 2 =>
          ∀ k, |ip (half 0 (fg (g k))) (half 0 (cMP ra.1 ra.2))| < 1 / (2 : ℝ) ^ ((d : ℝ) / 3)).card
        : ℝ) / (2 : ℝ) ^ (d + 1) := by sorry

end PrivLearn.MaskedParity
