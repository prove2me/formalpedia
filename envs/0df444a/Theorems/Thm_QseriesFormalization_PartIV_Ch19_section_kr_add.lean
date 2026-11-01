-- Prove2me | Theorems.Thm_QseriesFormalization_PartIV_Ch19_section_kr_add
-- name    : QseriesFormalization.PartIV.Ch19.section_kr_add
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T10:00:21.475144+00:00
-- url     : https://prove2.me/theorems/29824f6a-9701-4f7a-a500-9812a187aa19
-- title:
--   The $(k,r)$-section is additive
-- statement:
--   For a commutative semiring $R$, $k,r\in\mathbb{N}$ and power series $\varphi,\psi\in R[[X]]$,
--   $$\mathrm{section}_{k,r}(\varphi+\psi)=\mathrm{section}_{k,r}(\varphi)+\mathrm{section}_{k,r}(\psi),$$
--   where `section_kr` $R\,k\,r\,\varphi=\sum_n[X^{kn+r}]\varphi\,X^n$. Basic property from Chapter 19.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 19. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter19_Section5.lean#L44-L49

import Definitions.Def_QseriesFormalization_Chapter19_Section5
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

open QseriesFormalization
open QseriesFormalization.PartIV
open QseriesFormalization.PartIV.Ch19

open PowerSeries

theorem QseriesFormalization.PartIV.Ch19.section_kr_add (R : Type*) [CommSemiring R] (k r : ℕ)
    (φ ψ : PowerSeries R) :
    section_kr R k r (φ + ψ) = section_kr R k r φ + section_kr R k r ψ := by sorry
