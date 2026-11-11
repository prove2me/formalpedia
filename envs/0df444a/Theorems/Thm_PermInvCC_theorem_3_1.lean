-- Prove2me | Theorems.Thm_PermInvCC_theorem_3_1
-- name    : PermInvCC.theorem_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:27:53.572647+00:00
-- url     : https://prove2.me/theorems/f59536d0-5963-41d9-b99d-bba31747e2a3
-- title:
--   Theorem 3.1 — classical upper bound $R^{\mathrm{pub}}(f)\le C_q\,u\log(2+n/u)$, $u=\min\{n,h_f^{-2}\}$
-- statement:
--   For each $q\ge2$ there is a constant $C_q>0$ such that the following holds for every $n\ge2$. Let $\rho,\sigma$ be margins of total $n$ and let $f:[q]^n\times[q]^n\to\{-1,+1,*\}$ be permutation-invariant with every promised input having histograms $\rho,\sigma$ (so both parties know the margins). Then
--   $$R^{\mathrm{pub}}(f)\le C_q\,u\log(2+n/u),\qquad u:=\min\{n,h_f^{-2}\}.$$
--
--   This is the classical half of the main theorem: the cost is governed by the separation parameter.
--
--   Differences from the source:
--   - generalization: R^pub with Bob producing the output → R^pub with the output determined by the transcript (both parties output); reason: the Lean complexity is at least the paper's, so the Lean upper bound implies the paper's; it is still true because both-party output costs at most one more bit, absorbed by C_q
--   - encoding: f restricted to the margins ρ, σ known to both parties → hypothesis: every promised input has histograms ρ, σ; reason: a protocol for this f may use ρ, σ; knowing them adds nothing
--   - encoding: logarithms base two → Real.logb 2; reason: Lean notation; same values
-- source:
--   Huang and Ye, Quantum Advantage of Permutation-Invariant Functions in Communication Complexity, arXiv:2609.40116 (held version, sha256 fe1797dd…), Theorem 3.1, p.11 (proof pp.13–14)

import Mathlib
import Definitions.Def_PermInvCC_PartialFn
import Definitions.Def_PermInvCC_IsPermInvariant
import Definitions.Def_PermInvCC_jointType
import Definitions.Def_PermInvCC_hg
import Definitions.Def_PermInvCC_Rpub

namespace PermInvCC

/-- **Theorem 3.1 (Classical Upper Bound)** (Y. Huang and Z. Ye, arXiv:2609.40116, held version
sha256 fe1797dd…, p.11). Suppose both parties know the margins `ρ, σ`. For a
permutation-invariant partial function `f` restricted to these margins, let `h_f` be as in
Definition 2.4. Then `R^pub(f) ≤ C_q u log(2 + n/u)` with `u := min{n, h_f^{−2}}`.

**Formalization Note.** `C_q` is chosen after `q` and before `n`, the margins and `f` (p.21:
"Let `K_q` denote the constant in Theorem 3.1"). "Restricted to these margins" is the hypothesis
that every promised input has histograms `ρ, σ`; a protocol for this `f` may use `ρ, σ`, so
"both parties know the margins" adds nothing. `R^pub` uses transcript-determined output. Logs are
base two. -/
theorem theorem_3_1 (q : ℕ) (hq : 2 ≤ q) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n → ∀ ρ σ : Fin q → ℕ, ∑ a, ρ a = n → ∑ b, σ b = n →
      ∀ f : PartialFn n q, IsPermInvariant f →
        (∀ x y, f x y ≠ none → hist x = ρ ∧ hist y = σ) →
        let u : ℝ := min (n : ℝ) ((hg f)⁻¹ ^ 2)
        (Rpub f : ℝ) ≤ C * u * Real.logb 2 (2 + n / u) := by sorry

end PermInvCC
