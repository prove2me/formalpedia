-- Prove2me | Theorems.Thm_Pr6453Site_site_identities
-- name    : Pr6453Site.site_identities
-- status  : Proved
-- author  : @gustasmickus
-- created : 2026-11-09T09:08:33.771131+00:00
-- url     : https://prove2.me/theorems/74c53e8a-f577-410b-957d-54dc88b91f24
-- title:
--   PR #6453: the site identities of the root, from one conjugation lemma
-- statement:
--   The three site identities that module_check.py checks for every site of the PR #6453 root: from one conjugation lemma (c D ci)(c E ci) = c (D E) ci, a 0/1-diagonal stage projector is idempotent, the projector absorbs the query plane, and two stages with commuting supports commute.
-- source:
--   CrocSwap/integer-mult-bounds, PR #6453, head b1a3e525793eca35c56324aa7ffd0b714cf606d4, research/mixed-projector-query-root/module_check.py.

import Mathlib

set_option autoImplicit false

namespace Pr6453Site

open Matrix

theorem site_identities {n : Type*} [Fintype n] [DecidableEq n]
    (c ci : Matrix n n ℚ) (h : ci * c = 1) :
    (∀ d : n → ℚ, (∀ i, d i * d i = d i) →
        (c * diagonal d * ci) * (c * diagonal d * ci) = c * diagonal d * ci) ∧
      (∀ α β : Matrix n n ℚ, β * α = α →
        (c * β * ci) * (c * α * ci) = c * α * ci) ∧
      (∀ d e : n → ℚ, (∀ i, d i * e i = e i * d i) →
        (c * diagonal d * ci) * (c * diagonal e * ci)
          = (c * diagonal e * ci) * (c * diagonal d * ci)) := by
  sorry

end Pr6453Site
