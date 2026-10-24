-- Prove2me | Theorems.Thm_QseriesFormalization_PartIV_Ch17_jacobiTripleSign_nonzero_mod_11_residue
-- name    : QseriesFormalization.PartIV.Ch17.jacobiTripleSign_nonzero_mod_11_residue
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-23T09:34:48.13121+00:00
-- url     : https://prove2.me/theorems/5b01f796-2631-4189-a1a3-3c81356bf586
-- title:
--   Residues of $n$ mod 11 where the Jacobi sign coefficient is nonzero
-- statement:
--   Let `jacobiTripleSign` $J(n)$ be the integer defined by $J(n)=(-1)^k(2k+1)$ if $n=k(k+1)/2$ is the $k$-th triangular number, and $J(n)=0$ otherwise (the coefficient of $q^n$ in $\prod(1-q^m)^3$, Jacobi's identity). For every natural number $n$, if $J(n)\not\equiv0 \pmod{11}$ (as an element of $\mathbb{Z}/11$), then
--   $$n\equiv 0,1,3,6\text{ or }10 \pmod{11}.$$
--   This is a residue analysis used in Chapter 17's mod 11 argument for $p(11n+6)\equiv0\pmod{11}$.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 17. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter17_Mod11PerTermAnalysis.lean#L73-L101

import Definitions.Def_QseriesFormalization_DefCoreQSeries
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Combinatorics.Enumerative.Partition.GenFun
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Chapter 17 — Mod-11 per-term residue analysis

For Ramanujan's third congruence `∀ n, 11 ∣ p(11n + 6)`.

**Note**: unlike mod 5 / mod 7, a single per-term zero on convolution
`coeff (qPoch^k) (11n+6) ≠ 0` analysis does NOT close mod 11 — that would
require pentagonal-residue cancellation, but the relevant residue set
{0,1,3,6,10} can sum to 6 mod 11 in several ways.  So this file only
collects the basic mod-11 residue classification of `jacobiTripleSign`,
to be consumed by the Hirschhorn §3.5 J_i-decomposition.
-/

open QseriesFormalization
open QseriesFormalization.PartIV

open QseriesFormalization.PartIV.Ch19

theorem QseriesFormalization.PartIV.Ch17.jacobiTripleSign_nonzero_mod_11_residue (n : ℕ)
    (h : ((jacobiTripleSign n : ℤ) : ZMod 11) ≠ 0) :
    (n : ZMod 11) = 0 ∨ (n : ZMod 11) = 1 ∨ (n : ZMod 11) = 3 ∨
    (n : ZMod 11) = 6 ∨ (n : ZMod 11) = 10 := by sorry
