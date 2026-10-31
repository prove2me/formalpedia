-- Prove2me | Theorems.Thm_SVFAppt_theorem_3_4
-- name    : SVFAppt.theorem_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:22:46.123098+00:00
-- url     : https://prove2.me/theorems/b39393ab-4a59-45fa-8a3e-9e27f3210a6f
-- title:
--   Theorem 3.4 — under the dilation ordering, $\varrho_\omega\le4$
-- statement:
--   Let $B_1,\dots,B_n$ be independent service times with finite means $\mu_1,\dots,\mu_n$ on a probability space, satisfying the dilation ordering assumption
--
--   $$B_1\le_{\mathrm{dil}}B_2\le_{\mathrm{dil}}\cdots\le_{\mathrm{dil}}B_n,$$
--
--   and let $0\le\omega\le1$. Let $C_\omega(B,\tau,x)=\omega\sum_i\mathbb EI_i+(1-\omega)\sum_i\mathbb EW_i$ be the cost (2) of a sequence $\tau$ and schedule $x$, with waiting and idle times from the Lindley recursions (1). Then the smallest-variance-first sequence (the identity, under this numbering) with the mean-based schedule $x=\mu$ satisfies, for every sequence $\tau$,
--
--   $$C_\omega(B,\mathrm{id},\mu)\ \le\ 4\,C_\omega(B,\tau,\mu).$$
--
--   Equivalently, the approximation ratio $\varrho_\omega(B)=C_\omega(B,\mathrm{id},\mu)/\min_\tau C_\omega(B,\tau,\mu)$ is at most $4$.
--
--   Without an ordering assumption the ratio is unbounded (Example 2.2, which has independent symmetric service times), and Example 3.1 shows that ratios above $1.52$ occur under the dilation ordering.
--
--   **Formalization Note** Slots and patients are 0-based; the weight is `wt`.
--
--   Differences from the source:
--   - encoding: ϱ_ω = C_ω(id, µ) / min{C_ω(τ, µ) : τ ∈ S_n} ⩽ 4 → C_ω(id, µ) ⩽ 4 · C_ω(τ, µ) for every τ; reason: the minimum over the finite S_n is attained; same statement whenever it is positive, and it also covers the 0/0 case
--   - generalization: ω ∈ (0, 1) → 0 ⩽ ω ⩽ 1; reason: the proof uses only nonnegative weights; restricts to the printed range
--   - generalization: service times with means µ_i and variances σ_i² (nonnegative; Remark 2.1 allows negative values) → integrable real-valued service times, possibly negative, variances not assumed finite; reason: variances only label the svf order, which Assumption 2.4 already fixes; every finite-variance nonnegative instance is a special case
--   - encoding: independent random variables B_1, …, B_n with means µ_i → measurable, integrable B : Fin n → Ω → ℝ on a probability space with iIndepFun; reason: Lean convention for a finite family of real random variables with finite means
--   - encoding: slots and patients numbered 1, …, n → Fin n (0-based); Lean slot i is the paper's slot i + 1; reason: Lean convention; same instances
--   - reading: initial waiting and idle times not stated → W_0 = I_0 = 0 (the paper's W_1 = I_1 = 0); reason: the paper's identity (5) holds exactly under this convention; the first patient arrives to an idle doctor
-- source:
--   de Kemp, Mandjes, Olver, Performance of the Smallest-Variance-First Rule in Appointment Sequencing, arXiv:1812.01467v4, Theorem 3.4, p. 15 (ratio ϱ_ω pp. 8–9; Assumption 2.4 p. 11)

import Mathlib
import Definitions.Def_SVFAppt_mu
import Definitions.Def_SVFAppt_cost
import Definitions.Def_SVFAppt_DilationChain

open MeasureTheory ProbabilityTheory

namespace SVFAppt

/-- **Theorem 3.4: under the dilation ordering, svf with the mean-based schedule costs at most
four times any sequence.**
de Kemp, Mandjes, Olver, arXiv:1812.01467v4, Theorem 3.4, p. 15: "Under the dilation ordering
assumption, we have ϱω ⩽ 4", with (pp. 8–9) "ϱω(B) := Cω(B, id, µ) / min{Cω(B, τ, µ) : τ ∈ Sn}"
and Assumption 2.4 (p. 11) "We have B1 ⩽dil B2 ⩽dil . . . ⩽dil Bn."

Let `B 0, …, B (n−1)` be independent integrable service times on a probability space `(Ω, P)`
with `B 0 ⩽dil B 1 ⩽dil ⋯ ⩽dil B (n−1)`, and let `0 ⩽ ω ⩽ 1`. Then for every sequence `τ`,
`C_ω(B, id, µ) ⩽ 4 · C_ω(B, τ, µ)`, where `µ` is the vector of means and `C_ω` is the cost (2)
computed from the Lindley recursion (1).

**Formalization Note**
* `ϱ_ω ⩽ 4` is stated multiplicatively for every `τ`; since `S_n` is finite the minimum is
  attained, so this is the printed bound, and it also covers the case of minimum cost `0`.
* `ω ∈ [0, 1]` (the paper's `(0, 1)` plus its endpoints) and service times are only assumed
  integrable (they may be negative, Remark 2.1; finite variances are not assumed).
* 0-based slots and patients; the svf sequence is the identity because Assumption 2.4 numbers
  the patients. -/
theorem theorem_3_4 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (B : Fin n → Ω → ℝ) (hBm : ∀ j, Measurable (B j)) (hBi : ∀ j, Integrable (B j) P)
    (hind : iIndepFun B P) (hdil : DilationChain P B)
    (wt : ℝ) (hwt0 : 0 ≤ wt) (hwt1 : wt ≤ 1) :
    ∀ τ : Equiv.Perm (Fin n), cost P B wt 1 (mu P B) ≤ 4 * cost P B wt τ (mu P B) := by sorry

end SVFAppt
