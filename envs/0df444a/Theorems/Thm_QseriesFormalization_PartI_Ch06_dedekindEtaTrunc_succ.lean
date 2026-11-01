-- Prove2me | Theorems.Thm_QseriesFormalization_PartI_Ch06_dedekindEtaTrunc_succ
-- name    : QseriesFormalization.PartI.Ch06.dedekindEtaTrunc_succ
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T10:35:09.747034+00:00
-- url     : https://prove2.me/theorems/ec80d460-4673-43a7-8c0d-55f392926c18
-- title:
--   Recursion for the truncated eta-product $(q;q)_N$
-- statement:
--   Let $R$ be a field, $q\in R$, $N\in\mathbb{N}$. The truncated Dedekind-eta-type product, defined here as the finite product $\eta_N(q)=(q;q)_N=\prod_{m=1}^{N}(1-q^m)$ (without the fractional prefactor $q^{1/24}$), satisfies
--   $$\eta_{N+1}(q)=\eta_N(q)\,(1-q^{N+1}).$$
--   This is a basic recursion for the finite products used in Chapter 6.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 6. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter06.lean#L59-L63

import Definitions.Def_QseriesFormalization_Chapter06
import Mathlib
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Chapter 6 — Macdonald's identities (Chan §6) — **MISLABELED**

⚠️  **MISLABELED CHAPTER**.

Per `PLAYBOOK_AUDIT.md` (2026-05-22), after cross-checking Chan's TOC and
Chapter 6 text:

**Chan §6 is "Macdonald's identities".**  Its main result is
**Theorem 6.1**:

    η(q)^{t²-1}  =  c_0 · ∑_{(v_0,…,v_{t-1}) ∈ ℤ^t, v_i ≡ i (mod t),
                              v_0+…+v_{t-1}=0}
                     ∏_{i<j} (v_i − v_j) · q^{(v_0² + … + v_{t-1}²)/(2t)}

    where η(q) := q^{1/24} · ∏_{m≥1} (1 − q^m)  is the Dedekind η-function
    and t is an odd positive integer.  This is the Weyl-Macdonald-Kac
    denominator formula for the affine Lie algebra ŝl(2,ℂ).

**What this file actually contains** is just the polynomial truncation
`dedekindEtaTrunc q N := (q;q)_N` (without the `q^{1/24}` prefactor) and
its `_succ`/`_one` recursion.  That is **not** Chan §6 — it is just the
plain finite product `(q;q)_N`, which already lives in `Basic.lean`.

So Chan §6's Macdonald's identity (Theorem 6.1) was originally **completely
absent from this repository**.  The plain `dedekindEtaTrunc q N := (q;q)_N`
content below is unrelated finite-product scaffolding.

**Update (2026-05-24)**: the foundational `t = 2` (affine `A₁`, `ŝl(2,ℂ)`)
case of Macdonald's identity — i.e. **Jacobi's identity**
`(q;q)_∞³ = ∑_{k≥0} (-1)^k (2k+1) q^{k(k+1)/2}` — is now formalized and
proven **unconditionally** in `Pending/Chapter06_Macdonald_A1.lean`
(`macdonald_A1_identity`), as a corollary of the formal-PS Jacobi cube
identity B2.  The general odd-`t` Macdonald denominator formula (needing
affine Lie theory) remains open.
-/

open QseriesFormalization
open QseriesFormalization.PartI
open QseriesFormalization.PartI.Ch06

variable {R : Type*} [Field R]

theorem QseriesFormalization.PartI.Ch06.dedekindEtaTrunc_succ (q : R) (N : Nat) :
    dedekindEtaTrunc q (N + 1) =
      dedekindEtaTrunc q N * (1 - q ^ (N + 1)) := by sorry
