-- Prove2me | Theorems.Thm_ProcFlex_DMGI_lemma_3b
-- name    : ProcFlex.DMGI.lemma_3b
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:24:57.179899+00:00
-- url     : https://prove2.me/theorems/ab4b58a3-d944-4675-ad0e-104f2741a137
-- title:
--   Lemma 3(b): an even balanced cyclic window
-- statement:
--   In a cyclic ordering of $2k$ products with exactly $k$ high-margin products, take any integer $\ell$ satisfying $1\le\ell\le k$. Some consecutive cyclic window of length $2\ell$ contains exactly $\ell$ high-margin and $\ell$ low-margin products:
--
--   $$
--   \exists s,\quad \#\{q\in\{0,\ldots,2\ell-1\}:c(s+q\bmod 2k)=H\}=\ell.
--   $$
--
--   This is the even-window companion to Lemma 3(a).
--
--   **Formalization Note** A Boolean colouring abstracts the high/low product categories; the window runs cyclically and may wrap.
-- source:
--   Wang, Wang & Zhang, Robust Optimization Approach to Process Flexibility Designs with Contribution Margin Differentials, SSRN 3233721 (version of 22 May 2020), p. 46, Lemma 3(b)

import Mathlib

namespace ProcFlex.DMGI

open Finset

/-- Lemma 3(b), p. 46: an even cyclic window in a balanced high-low sequence. -/
theorem lemma_3b (k : ℕ) (hk : 1 ≤ k)
    (c : Fin (2 * k) → Bool)
    (hc : (univ.filter (fun i => c i = true)).card = k)
    (l : ℕ) (hl : 1 ≤ l) (hlu : l ≤ k) :
    ∃ s : Fin (2 * k),
      ((range (2 * l)).filter
        (fun q : ℕ => c ⟨(s.val + q) % (2 * k), Nat.mod_lt _ (by omega)⟩ = true)).card = l := by sorry

end ProcFlex.DMGI
