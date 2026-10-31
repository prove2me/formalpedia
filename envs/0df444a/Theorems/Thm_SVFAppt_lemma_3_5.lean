-- Prove2me | Theorems.Thm_SVFAppt_lemma_3_5
-- name    : SVFAppt.lemma_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:22:46.110954+00:00
-- url     : https://prove2.me/theorems/784689fe-1d97-4560-845d-35a4a5d0b9d6
-- title:
--   Lemma 3.5 — a per-slot bound against constrained sequences bounds the approximation ratio
-- statement:
--   Let $B_1,\dots,B_n$ be independent integrable service times satisfying the dilation ordering assumption $B_1\le_{\mathrm{dil}}\cdots\le_{\mathrm{dil}}B_n$, use the mean-based schedule $x=\mu$, and let $0\le\omega\le1$ and $\varrho'\ge0$. For a slot $k\in\{1,\dots,n-1\}$ let $\mathbb EW^{\mathrm{opt}'}_{k+1}$ be the smallest expected waiting time of the patient in slot $k+1$ over the sequences $\sigma$ that put patients $1,\dots,k$ in the first $k$ slots ($\sigma(i)\le k$ for $i\le k$). Suppose that for every such $k$
--
--   $$\mathbb E W^{\mathrm{svf}}_{k+1}\ \le\ \varrho'\,\mathbb EW^{\mathrm{opt}'}_{k+1}.$$
--
--   Then for every sequence $\tau$,
--
--   $$C_\omega(B,\mathrm{id},\mu)\ \le\ \varrho'\,C_\omega(B,\tau,\mu),$$
--
--   that is, $\varrho_\omega\le\varrho'$.
--
--   This reduces the approximation ratio to a slot-by-slot comparison of expected waiting times, in which the competitor may be assumed to keep the $k$ least variable patients in the first $k$ slots.
--
--   **Formalization Note** 0-based slots and patients. The hypothesis is stated against every admissible $\sigma$, which is equivalent to the bound against the minimum (attained over a finite set).
--
--   Differences from the source:
--   - encoding: ratio hypothesis EW^svf_{k+1}/EW^opt′_{k+1} ⩽ ϱ′ for all k, with EW^opt′ a minimum over constrained sequences → EW^id_k ⩽ ϱ′ · EW^σ_k for every 1 ⩽ k < n and every σ with σ(i) < k for i < k; reason: the minimum over the finite admissible set is attained; the multiplicative form also fixes the 0/0 case
--   - encoding: conclusion ϱ_ω ⩽ ϱ′ (a ratio with the minimum over S_n in the denominator) → C_ω(id, µ) ⩽ ϱ′ · C_ω(τ, µ) for every τ; reason: the minimum over the finite S_n is attained; same statement whenever it is positive, and covers the 0/0 case
--   - encoding: ϱ′ unconstrained → 0 ⩽ ϱ′; reason: a ratio of nonnegative expectations is never below 0, so ϱ′ < 0 admits no instance with defined ratios; without it the multiplicative form fails (n = 2, X_1 = 0, X_2 = ±1, ϱ′ = −1)
--   - generalization: ω ∈ (0, 1) → 0 ⩽ ω ⩽ 1; reason: the proof uses only nonnegative weights; restricts to the printed range
--   - generalization: service times with means µ_i and variances σ_i² (nonnegative; Remark 2.1 allows negative values) → integrable real-valued service times, possibly negative, variances not assumed finite; reason: variances only label the svf order, which Assumption 2.4 already fixes; every finite-variance nonnegative instance is a special case
--   - encoding: independent random variables B_1, …, B_n with means µ_i → measurable, integrable B : Fin n → Ω → ℝ on a probability space with iIndepFun; reason: Lean convention for a finite family of real random variables with finite means
--   - encoding: slots and patients numbered 1, …, n → Fin n (0-based); Lean slot i is the paper's slot i + 1; reason: Lean convention; same instances
--   - reading: initial waiting and idle times not stated → W_0 = I_0 = 0 (the paper's W_1 = I_1 = 0); reason: the paper's identity (5) holds exactly under this convention; the first patient arrives to an idle doctor
-- source:
--   de Kemp, Mandjes, Olver, Performance of the Smallest-Variance-First Rule in Appointment Sequencing, arXiv:1812.01467v4, Lemma 3.5, p. 15

import Mathlib
import Definitions.Def_SVFAppt_lindley
import Definitions.Def_SVFAppt_mu
import Definitions.Def_SVFAppt_cost
import Definitions.Def_SVFAppt_DilationChain

open MeasureTheory ProbabilityTheory

namespace SVFAppt

/-- **Lemma 3.5: a per-slot bound against constrained sequences bounds the ratio.**
de Kemp, Mandjes, Olver, arXiv:1812.01467v4, Lemma 3.5, p. 15: "Let EW opt′ k+1 denote the
expected waiting time of the patient in appointment slot k + 1, under the sequence that minimizes
this expected waiting time, subject to the constraint that τ(i) ⩽ k for all i = 1, . . . , k, i.e.
the first k patients are assigned to the first k slots. Suppose EW svf k+1/EW opt′ k+1 ⩽ ϱ′ for all
k. Then, under the dilation ordering assumption, ϱω ⩽ ϱ′."

Let `B 0, …, B (n−1)` be independent integrable service times on a probability space `(Ω, P)`
with `B 0 ⩽dil ⋯ ⩽dil B (n−1)`, let `0 ⩽ ω ⩽ 1` and `0 ⩽ ϱ′`. Suppose that for every slot
`1 ⩽ k < n` and every sequence `σ` whose first `k` slots hold exactly the patients `0, …, k−1`,
`E W^{id}_k ⩽ ϱ′ · E W^{σ}_k` under the mean-based schedule. Then for every sequence `τ`,
`C_ω(id, µ) ⩽ ϱ′ · C_ω(τ, µ)`.

**Formalization Note** 0-based slots and patients (Lean `W_k` is the paper's `W_{k+1}`). The
ratio hypothesis `EW^svf/EW^opt′ ⩽ ϱ′` is stated multiplicatively against every admissible `σ`
(the minimum over the finite admissible set is attained), and the conclusion `ϱ_ω ⩽ ϱ′` is stated
multiplicatively against every `τ`. `0 ⩽ ϱ′` is needed for the multiplicative form: a ratio of
nonnegative costs is never below `0`. -/
theorem lemma_3_5 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (B : Fin n → Ω → ℝ) (hBm : ∀ j, Measurable (B j)) (hBi : ∀ j, Integrable (B j) P)
    (hind : iIndepFun B P) (hdil : DilationChain P B)
    (wt : ℝ) (hwt0 : 0 ≤ wt) (hwt1 : wt ≤ 1) (ρ' : ℝ) (hρ' : 0 ≤ ρ')
    (hslot : ∀ k : ℕ, 1 ≤ k → k < n → ∀ σ : Equiv.Perm (Fin n),
      (∀ i : Fin n, i.val < k → (σ i).val < k) →
        ∫ s, wait 1 (mu P B) (fun j => B j s) k ∂P ≤
          ρ' * ∫ s, wait σ (mu P B) (fun j => B j s) k ∂P) :
    ∀ τ : Equiv.Perm (Fin n), cost P B wt 1 (mu P B) ≤ ρ' * cost P B wt τ (mu P B) := by sorry

end SVFAppt
