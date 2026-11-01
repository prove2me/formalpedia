-- Prove2me | Theorems.Thm_QseriesFormalization_PartIV_Ch19_coeff_section_kr
-- name    : QseriesFormalization.PartIV.Ch19.coeff_section_kr
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T09:52:47.469993+00:00
-- url     : https://prove2.me/theorems/812c7620-05da-4c5d-95b4-94efbfd51691
-- title:
--   Coefficients of the $(k,r)$-section of a power series
-- statement:
--   Let $R$ be a commutative semiring, $k,r,n\in\mathbb{N}$ and $\varphi\in R[[X]]$. The $(k,r)$-section `section_kr` $R\,k\,r\,\varphi$ is the power series whose $n$-th coefficient is the $(kn+r)$-th coefficient of $\varphi$. The statement is the defining coefficient formula
--   $$[X^n]\,\mathrm{section}_{k,r}(\varphi)=[X^{kn+r}]\,\varphi.$$
--   This section operator is the tool used in Chapter 19 to express arithmetic-progression congruences as power-series identities.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 19. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter19_Section5.lean#L36-L42

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

theorem QseriesFormalization.PartIV.Ch19.coeff_section_kr (R : Type*) [CommSemiring R] (k r n : ℕ)
    (φ : PowerSeries R) :
    PowerSeries.coeff (R := R) n (section_kr R k r φ) =
      PowerSeries.coeff (R := R) (k * n + r) φ := by sorry
