-- Prove2me | Theorems.Thm_RuntimeTransfer_oracle_substitution
-- name    : RuntimeTransfer.oracle_substitution
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T11:14:08.745077+00:00
-- url     : https://prove2.me/theorems/c00faf58-a6c8-48c1-95a7-19220f445bb5
-- title:
--   Correctness and the sum of query costs
-- statement:
--   For any oracle program, if a costed oracle returns the specified answer on every query and each query cost is bounded by the supplied function, execution returns the specification-selected value and costs at most the specified-path budget. The budget sums explicit local-work labels and the individual query bounds.
-- source:
--   General runtime transfer and its Fourier/packing applications, companion proof note for this mission, 24 October 2026. Original cost-semantics formulation of standard substitution principles; not a claimed new complexity bound. Theorem 1, sum-of-individual-query-bounds version.

import Definitions.Def_RuntimeTransfer
set_option autoImplicit false
open RuntimeTransfer

theorem RuntimeTransfer.oracle_substitution {Q A R : Type} (p : Program Q A R)
    (spec : Q → A) (oracle : Q → A × ℕ) (bound : Q → ℕ)
    (hcorrect : ∀ q, (oracle q).1 = spec q)
    (hcost : ∀ q, (oracle q).2 ≤ bound q) :
    (p.run oracle).1 = p.value spec ∧
      (p.run oracle).2 ≤ p.budget spec bound := by sorry
