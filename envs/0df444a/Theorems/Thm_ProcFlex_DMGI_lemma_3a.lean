-- Prove2me | Theorems.Thm_ProcFlex_DMGI_lemma_3a
-- name    : ProcFlex.DMGI.lemma_3a
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:24:55.261121+00:00
-- url     : https://prove2.me/theorems/543deda8-6b9a-4a3d-8c10-9ff97b3cfc88
-- title:
--   Lemma 3(a): an odd balanced cyclic window
-- statement:
--   In a cyclic ordering of $2k$ products with exactly $k$ high-margin products, take any integer $\ell$ satisfying $1\le\ell\le k-1$. Some consecutive cyclic window of length $2\ell+1$ has exactly $\ell$ high-margin and $\ell+1$ low-margin products:
--
--   $$
--   \exists s,\quad \#\{q\in\{0,\ldots,2\ell\}:c(s+q\bmod 2k)=H\}=\ell.
--   $$
--
--   This is the odd-window statement used in the comparison of long-chain arrangements.
--
--   **Formalization Note** A Boolean colouring abstracts the high/low product categories; `true` denotes high margin. The source's window is cyclic and may wrap past the last product.
-- source:
--   Wang, Wang & Zhang, Robust Optimization Approach to Process Flexibility Designs with Contribution Margin Differentials, SSRN 3233721 (version of 22 May 2020), p. 46, Lemma 3(a)

import Mathlib

namespace ProcFlex.DMGI

open Finset

/-- Lemma 3(a), p. 46: an odd cyclic window in a balanced high-low sequence. -/
theorem lemma_3a (k : ℕ) (hk : 1 ≤ k)
    (c : Fin (2 * k) → Bool)
    (hc : (univ.filter (fun i => c i = true)).card = k)
    (l : ℕ) (hl : 1 ≤ l) (hlu : l ≤ k - 1) :
    ∃ s : Fin (2 * k),
      ((range (2 * l + 1)).filter
        (fun q : ℕ => c ⟨(s.val + q) % (2 * k), Nat.mod_lt _ (by omega)⟩ = true)).card = l := by sorry

end ProcFlex.DMGI
