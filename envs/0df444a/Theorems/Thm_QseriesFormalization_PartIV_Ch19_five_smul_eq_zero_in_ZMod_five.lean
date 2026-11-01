-- Prove2me | Theorems.Thm_QseriesFormalization_PartIV_Ch19_five_smul_eq_zero_in_ZMod_five
-- name    : QseriesFormalization.PartIV.Ch19.five_smul_eq_zero_in_ZMod_five
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T09:54:51.311609+00:00
-- url     : https://prove2.me/theorems/2e094871-ca64-4d57-8005-b121e686ab46
-- title:
--   $5\cdot\varphi=0$ for power series over $\mathbb{Z}/5$
-- statement:
--   For every power series $\varphi\in(\mathbb{Z}/5)[[X]]$, the scalar multiple $5\cdot\varphi$ is $0$. This is used at the end of the Chapter 19 argument, where a prefactor $5$ on the right-hand side vanishes, yielding the congruence $5\mid p(5n+4)$.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 19. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter19_Section5.lean#L106-L117

import Mathlib.Combinatorics.Enumerative.Partition.GenFun
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Tactic.Linarith

/-!
# Chapter 19 — k-sections of power series (foundation for MBI / general Ramanujan)

To prove `∀ n, 5 ∣ p(5n+4)` and the other Ramanujan congruence families
unconditionally, we need Hirschhorn-style algebra on (ZMod p)⟦X⟧ that
extracts the coefficients in a fixed residue class.  The natural tool is
the **k-section operator** at residue r:

  section_kr φ := mk (fun n => coeff φ (k·n + r))

This file defines that operator and proves its basic algebraic properties.
These are foundation lemmas for the MBI proof (Pending/Chapter16_MBI.lean)
and for discharging the formal-PS vanishing hypothesis needed by Chapter
19's `ramanujan_from_pochInf_vanishes`.

All theorems in this file are unconditional (no sorry, no axiom beyond
the core three).
-/

open PowerSeries

theorem QseriesFormalization.PartIV.Ch19.five_smul_eq_zero_in_ZMod_five (φ : PowerSeries (ZMod 5)) :
    (5 : ZMod 5) • φ = 0 := by sorry
